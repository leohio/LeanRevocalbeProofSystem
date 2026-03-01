# Revocable Proof Systems — Lean 4 Formalization

Lean 4 による、Christ-Bonneau 2022 "Limits on revocable proof systems, with applications to stateless blockchains" の Theorem 1 の形式化プロジェクトです。

**論文**: Miranda Christ, Joseph Bonneau.
*"Limits on revocable proof systems, with applications to stateless blockchains"*
[ePrint 2022/1478](https://eprint.iacr.org/2022/1478) / [FC 2023 (Springer)](https://link.springer.com/chapter/10.1007/978-3-031-47751-5_4)

## 背景

ステートレスブロックチェーンでは、バリデータがグローバル状態（例: 未使用トランザクション出力の集合）を定数サイズのコミットメント（例: Merkle root）で管理し、ユーザーがトランザクションの正当性を証明する witness を提供します。

本論文は **Revocable Proof System (RPS)** という抽象概念を導入し、グローバル状態のサイズと witness 更新頻度の間にトレードオフが存在しないことを情報理論的に証明しています。グローバル状態をコンパクトに保つためには、ほぼ線形数の witness 更新が必要であり、逆に witness 更新を少なくするには線形サイズのグローバル状態が必要です。

## Theorem 1（原論文の記述）

> Let RPS = (Setup, ComputeState, Revoke, Verify) be a revocable proof system satisfying correctness, and let pp be any public parameters occurring with nonzero probability over Setup(1^λ). Let S be a set of size n, and let X\*\_k denote the set of subsets T ⊆ S that are k-good given RPS, S, and public parameters pp. Then |V|, the size of the global state in bits, satisfies:
>
> **|V| ≥ lg |X\*\_k| − ⌈k lg n⌉**

ここで k-good とは、集合 T を取り消した際に (1) 取り消された要素の証明が全て失敗し、(2) 取り消されていない要素のうち証明が変わるものが高々 k 個であることを意味します。

## 形式化の内容

### 定義 (`RevocableProofSystem/Defs.lean`)

公開パラメータ pp と初期状態 (V₀, π₁,...,πₙ) を固定した後の RPS を以下の 2 関数で抽象化しています:

```
structure RevocableProofSystem (S : Type*) (V : Type*) where
  revokedState : Finset S → V         -- T ↦ 更新後のグローバル状態 V'
  failingSet   : V → Finset S         -- V' ↦ {s ∈ S₀ : Verify(pp, V', s, πₛ) = false}
```

| 定義 | 対応する論文の概念 |
|---|---|
| `RevocableProofSystem S V` | 公開パラメータ固定後の RPS |
| `IsKGood rps S₀ k T` | Definition 3 (k-good revoked set) |
| `encode rps T` | 圧縮引数のエンコーダ A |
| `decode rps (v, L)` | 圧縮引数のデコーダ B |

### 証明 (`RevocableProofSystem/Theorem1.lean`)

論文のビット表現の定理と等価な、以下の **濃度形式** で Theorem 1 を証明しています:

> **|X\*\_k| ≤ |V\_type| × |{L ⊆ S₀ : |L| ≤ k}|**

ここで |V\_type| はグローバル状態の型の濃度（= 2^|V| に対応）です。

証明は論文と同じ圧縮引数 (compression argument) に従い、3 ステップで構成されます:

| ステップ | 補題 | 内容 |
|---|---|---|
| 1 | `decode_encode_eq` | k-good な T に対して decode(encode(T)) = T。`Finset.sdiff_sdiff_eq_self` を使用 |
| 2 | `encode_injOn` | ステップ 1 から encode の単射性を導出 |
| 3 | `theorem1` | 単射性 + 値域の有界性 → `Finset.card_le_card_of_injOn` で濃度不等式を結論 |

## ビルド方法

Lean 4 のバージョン管理ツール [elan](https://github.com/leanprover/elan) がインストール済みであることを前提とします。

```bash
# 依存関係の取得（Mathlib のキャッシュ含む）
lake update

# ビルド
lake build
```

## プロジェクト構成

```
.
├── lakefile.lean                      # Lake ビルド設定（Mathlib 依存）
├── lean-toolchain                     # Lean バージョン (v4.16.0)
├── RevocableProofSystem.lean          # ルートモジュール
└── RevocableProofSystem/
    ├── Defs.lean                      # RPS 定義、k-good、encode/decode
    └── Theorem1.lean                  # Theorem 1 の証明
```

## 参考文献

- Miranda Christ, Joseph Bonneau. "Limits on revocable proof systems, with applications to stateless blockchains." *Financial Cryptography and Data Security (FC 2023)*, LNCS 13951, Springer. [ePrint](https://eprint.iacr.org/2022/1478)
