import LeanAideCore
import Mathlib
set_option linter.style.commandStart false
set_option linter.style.longLine false

#leanaide_connect "http://drongo:8042"

/-
### Theorem:
Let $T : V \to V$ be a linear transformation on a finite-dimensional vector space
satisfying $T^2 = T$.
Let $\lambda$ be a scalar with $\lambda \neq 0,1$.
Define
\[
S = T - \lambda I.
\]
Prove that $S$ is invertible.

### Proof:

Assume that $V$ is a finite-dimensional vector space and that $T : V \to V$ is a linear map satisfying $T^2 = T$. Let $\lambda$ be a scalar with $\lambda \neq 0$ and $\lambda \neq 1$, and define $S = T - \lambda I$, where $I : V \to V$ denotes the identity map.

First, note that the condition $T^2 = T$ implies that for every $v \in V$ we have $T(T(v)) = T(v)$. In particular, if $v \in \operatorname{im}(T)$, then there exists $u \in V$ such that $v = T(u)$, and hence
\[
T(v) = T(T(u)) = T(u) = v.
\]
Therefore $T$ restricts to the identity map on $\operatorname{im}(T)$.

Next, we show that every vector $v \in V$ can be written as a sum of a vector in $\ker(T)$ and a vector in $\operatorname{im}(T)$. Let $v \in V$ be arbitrary and define
\[
w := v - T(v).
\]
Then
\[
T(w) = T(v - T(v)) = T(v) - T(T(v)) = T(v) - T(v) = 0,
\]
so $w \in \ker(T)$. By definition, $T(v) \in \operatorname{im}(T)$. Hence every $v \in V$ can be written as
\[
v = w + T(v)
\]
with $w \in \ker(T)$ and $T(v) \in \operatorname{im}(T)$, which shows that
\[
V = \ker(T) + \operatorname{im}(T).
\]

We now prove that the sum $\ker(T) + \operatorname{im}(T)$ is direct. Let $v \in \ker(T) \cap \operatorname{im}(T)$. Since $v \in \ker(T)$, we have $T(v) = 0$. Since $v \in \operatorname{im}(T)$, we have seen above that $T(v) = v$. Combining these equalities, we obtain
\[
v = T(v) = 0.
\]
Thus $\ker(T) \cap \operatorname{im}(T) = \{0\}$, and hence
\[
V = \ker(T) \oplus \operatorname{im}(T).
\]

We describe the action of $S$ on $\ker(T)$ and on $\operatorname{im}(T)$. Let $v \in \ker(T)$. Then $T(v) = 0$, and therefore
\[
S(v) = (T - \lambda I)(v) = T(v) - \lambda v = 0 - \lambda v = -\lambda v.
\]
Thus $S$ acts on $\ker(T)$ as multiplication by the scalar $-\lambda$. Since $\lambda \neq 0$, the scalar $-\lambda$ is invertible, and hence the restriction of $S$ to $\ker(T)$ is an invertible linear map from $\ker(T)$ to itself.

Similarly, let $v \in \operatorname{im}(T)$. Then, as shown above, $T(v) = v$, and therefore
\[
S(v) = (T - \lambda I)(v) = T(v) - \lambda v = v - \lambda v = (1 - \lambda)v.
\]
Thus $S$ acts on $\operatorname{im}(T)$ as multiplication by the scalar $1 - \lambda$. Since $\lambda \neq 1$, the scalar $1 - \lambda$ is invertible, and hence the restriction of $S$ to $\operatorname{im}(T)$ is an invertible linear map from $\operatorname{im}(T)$ to itself.

Because $V$ is the internal direct sum
\[
V = \ker(T) \oplus \operatorname{im}(T),
\]
every vector $v \in V$ can be written uniquely as $v = x + y$ with $x \in \ker(T)$ and $y \in \operatorname{im}(T)$. On such a decomposition, the map $S$ is given by
\[
S(v) = S(x + y) = S(x) + S(y) = -\lambda x + (1 - \lambda)y.
\]
The map $S$ is block-diagonal with respect to the decomposition $V = \ker(T) \oplus \operatorname{im}(T)$, with invertible diagonal blocks $-\lambda \cdot \operatorname{id}_{\ker(T)}$ on $\ker(T)$ and $(1 - \lambda) \cdot \operatorname{id}_{\operatorname{im}(T)}$ on $\operatorname{im}(T)$. A linear map that is invertible on each direct summand of a direct sum decomposition, and preserves that decomposition in this way, is invertible on the whole space.

More explicitly, define a linear map $R : V \to V$ as follows. For $v \in V$, write uniquely $v = x + y$ with $x \in \ker(T)$ and $y \in \operatorname{im}(T)$, and set
\[
R(v) := -\tfrac{1}{\lambda}x + \tfrac{1}{1 - \lambda}y.
\]
This is well-defined and linear because the decomposition is direct and the coefficients are scalars. Then, for such $v = x + y$, we compute
\[
S(R(v)) = S\bigl(-\tfrac{1}{\lambda}x + \tfrac{1}{1 - \lambda}y\bigr)
= -\lambda\bigl(-\tfrac{1}{\lambda}x\bigr) + (1 - \lambda)\bigl(\tfrac{1}{1 - \lambda}y\bigr)
= x + y
= v,
\]
and
\[
R(S(v)) = R\bigl(-\lambda x + (1 - \lambda)y\bigr)
= -\tfrac{1}{\lambda}(-\lambda x) + \tfrac{1}{1 - \lambda}((1 - \lambda)y)
= x + y
= v.
\]
Thus $R$ is both a left and right inverse of $S$, so $S$ is invertible.

-/

-- ### JSON Structured Proof

def example22 := json% {
  "document": {
    "type": "document",
    "body": [
      {
        "type": "Theorem",
        "header": "Theorem",
        "label": "thm:projection_shift_invertible",
        "hypothesis": [
          {
            "type": "let_statement",
            "variable_name": "V",
            "variable_type": "finite-dimensional vector space",
            "statement": "Assume that V is a finite-dimensional vector space."
          },
          {
            "type": "let_statement",
            "variable_name": "T",
            "variable_type": "linear map T : V → V",
            "properties": "T^2 = T",
            "statement": "Assume that T : V → V is a linear map satisfying T^2 = T."
          },
          {
            "type": "let_statement",
            "variable_name": "λ",
            "variable_type": "scalar",
            "properties": "λ ≠ 0 and λ ≠ 1",
            "statement": "Let λ be a scalar with λ ≠ 0 and λ ≠ 1."
          },
          {
            "type": "let_statement",
            "variable_name": "S",
            "variable_type": "linear map S : V → V",
            "value": "T - λ I",
            "statement": "Define S = T - λ I, where I : V → V is the identity map."
          }
        ],
        "claim": "The linear map S = T - λ I is invertible.",
        "proof": [
          {
            "type": "assert_statement",
            "claim": "For every v ∈ V we have T(T(v)) = T(v), and in particular for every v in im(T) we have T(v) = v.",
            "proof_method": "direct computation from T^2 = T",
            "results_used": [
              {
                "statement": "T^2 = T"
              }
            ]
          },
          {
            "type": "assert_statement",
            "claim": "For every v ∈ V, if v ∈ im(T) then T(v) = v.",
            "proof_method": "apply T to v = T(u) for some u ∈ V and use T^2 = T",
            "results_used": [
              {
                "statement": "If v = T(u) for some u ∈ V, then T(v) = T(T(u)) = T(u) = v, so T acts as the identity on im(T)."
              }
            ]
          },
          {
            "type": "assert_statement",
            "claim": "For every v ∈ V, the vector w := v - T(v) lies in ker(T).",
            "proof_method": "direct computation",
            "results_used": [
              {
                "statement": "T(w) = T(v - T(v)) = T(v) - T(T(v)) = T(v) - T(v) = 0, hence w ∈ ker(T)."
              }
            ]
          },
          {
            "type": "assert_statement",
            "claim": "Every v ∈ V can be written as v = w + T(v) with w ∈ ker(T) and T(v) ∈ im(T), so V = ker(T) + im(T).",
            "proof_method": "use the decomposition v = (v - T(v)) + T(v)",
            "results_used": [
              {
                "statement": "For each v ∈ V, w = v - T(v) ∈ ker(T) and T(v) ∈ im(T), so v is a sum of an element of ker(T) and an element of im(T)."
              }
            ]
          },
          {
            "type": "assert_statement",
            "claim": "ker(T) ∩ im(T) = {0}.",
            "proof_method": "direct argument using T(v) = 0 and T(v) = v",
            "results_used": [
              {
                "statement": "If v ∈ ker(T) ∩ im(T), then T(v) = 0 since v ∈ ker(T), and T(v) = v since v ∈ im(T); hence v = 0."
              }
            ]
          },
          {
            "type": "assert_statement",
            "claim": "V = ker(T) ⊕ im(T).",
            "proof_method": "show the sum is direct and equals V",
            "results_used": [
              {
                "statement": "V = ker(T) + im(T) and ker(T) ∩ im(T) = {0} together imply V = ker(T) ⊕ im(T)."
              }
            ]
          },
          {
            "type": "assert_statement",
            "claim": "For every v ∈ ker(T), S(v) = -λ v, so S acts on ker(T) as multiplication by the scalar -λ.",
            "proof_method": "direct computation",
            "results_used": [
              {
                "statement": "If v ∈ ker(T), then T(v) = 0, so S(v) = (T - λ I)(v) = T(v) - λ v = -λ v."
              }
            ]
          },
          {
            "type": "assert_statement",
            "claim": "The restriction of S to ker(T) is an invertible linear map from ker(T) to itself.",
            "proof_method": "scalar multiplication by a nonzero scalar is invertible",
            "results_used": [
              {
                "statement": "Since λ ≠ 0, the scalar -λ is invertible, so the map v ↦ -λ v on ker(T) is invertible."
              }
            ]
          },
          {
            "type": "assert_statement",
            "claim": "For every v ∈ im(T), S(v) = (1 - λ) v, so S acts on im(T) as multiplication by the scalar 1 - λ.",
            "proof_method": "direct computation using T(v) = v on im(T)",
            "results_used": [
              {
                "statement": "If v ∈ im(T), then T(v) = v, so S(v) = (T - λ I)(v) = T(v) - λ v = v - λ v = (1 - λ) v."
              }
            ]
          },
          {
            "type": "assert_statement",
            "claim": "The restriction of S to im(T) is an invertible linear map from im(T) to itself.",
            "proof_method": "scalar multiplication by a nonzero scalar is invertible",
            "results_used": [
              {
                "statement": "Since λ ≠ 1, the scalar 1 - λ is invertible, so the map v ↦ (1 - λ) v on im(T) is invertible."
              }
            ]
          },
          {
            "type": "assert_statement",
            "claim": "With respect to the direct sum decomposition V = ker(T) ⊕ im(T), the map S is block-diagonal with diagonal blocks -λ · id_{ker(T)} on ker(T) and (1 - λ) · id_{im(T)} on im(T).",
            "proof_method": "use the decomposition v = x + y with x ∈ ker(T), y ∈ im(T) and linearity of S",
            "results_used": [
              {
                "statement": "For v = x + y with x ∈ ker(T), y ∈ im(T), we have S(v) = S(x) + S(y) = -λ x + (1 - λ) y."
              }
            ]
          },
          {
            "type": "assert_statement",
            "claim": "There exists a linear map R : V → V such that R is both a left and right inverse of S.",
            "proof_method": "define R on the direct sum decomposition and verify SR = RS = id_V",
            "results_used": [
              {
                "statement": "For v = x + y with x ∈ ker(T), y ∈ im(T), define R(v) = -1/λ x + 1/(1 - λ) y; then S(R(v)) = v and R(S(v)) = v."
              }
            ]
          },
          {
            "type": "conclude_statement",
            "claim": "S is invertible as a linear map V → V.",
            "results_used": [
              {
                "statement": "A linear map with a two-sided inverse is invertible."
              }
            ]
          }
        ]
      }
    ]
  }
}


-- ## LeanCode generated by LeanAide
/-
theorem is_unit_sub_smul_id_of_is_idempotent_of_ne_zero_of_ne_one :
      ∀ {K : Type u} {V : Type v} [inst : Field K] [inst_1 : AddCommGroup V] [inst_2 : Module K V]
        [FiniteDimensional K V] {T : V →ₗ[K] V},
        T * T = T → ∀ {μ : K}, μ ≠ (0 : K) → μ ≠ (1 : K) → IsUnit (T - μ • (1 : V →ₗ[K] V)) :=
    by
    intro K V inst inst_1 inst_2 inst_7439058897038094550 T hT μ hμ0 hμ1
    have assert_9640271237634751201 :
      ∀ [inst : DivisionRing K] [inst_1 : AddCommGroup V] [inst_2 : Module K V]
        [FiniteDimensional K V] (T : V →ₗ[K] V),
        T * T = T →
          ∀ (μ : K),
            μ ≠ (0 : K) →
              μ ≠ (1 : K) →
                (∀ (v : V), (T : V → V) ((T : V → V) v) = (T : V → V) v) ∧
                  ∀ v ∈ LinearMap.range T, (T : V → V) v = v :=
      by repeat (sorry)
    have assert_290240271064752550 :
      ∀ [inst : DivisionRing K] [inst_1 : AddCommGroup V] [inst_2 : Module K V]
        [FiniteDimensional K V] (T : V →ₗ[K] V),
        T ∘ₗ T = T →
          ∀ (μ : K), μ ≠ (0 : K) → μ ≠ (1 : K) → ∀ v ∈ LinearMap.range T, (T : V → V) v = v :=
      by repeat (sorry)
    have assert_11918856549779650521 :
      ∀ [inst : DivisionRing K] [inst_1 : AddCommGroup V] [inst_2 : Module K V]
        [FiniteDimensional K V] (T : V →ₗ[K] V),
        T * T = T →
          ∀ (c : K),
            c ≠ (0 : K) →
              c ≠ (1 : K) →
                ∀ (μ : K),
                  μ ≠ (0 : K) → μ ≠ (1 : K) → ∀ (v : V), v - (T : V → V) v ∈ LinearMap.ker T :=
      by repeat (sorry)
    have assert_5323617169768303690 :
      ∀ [inst : DivisionRing K] [inst_1 : AddCommGroup V] [inst_2 : Module K V]
        [FiniteDimensional K V] (T : V →ₗ[K] V),
        T * T = T → LinearMap.ker T ⊔ LinearMap.range T = ⊤ :=
      by repeat (sorry)
    have assert_3605381847287387093 :
      ∀ [inst : DivisionRing K] [inst_1 : AddCommGroup V] [inst_2 : Module K V]
        [FiniteDimensional K V] (T : V →ₗ[K] V),
        T * T = T →
          ∀ (la mu : K),
            la ≠ (0 : K) →
              la ≠ (1 : K) →
                mu ≠ (0 : K) → mu ≠ (1 : K) → LinearMap.ker T ⊓ LinearMap.range T = ⊥ :=
      by repeat (sorry)
    have assert_10502880745762333757 :
      ∀ [inst : DivisionRing K] [inst_1 : AddCommGroup V] [inst_2 : Module K V]
        [FiniteDimensional K V] (T : V →ₗ[K] V),
        T * T = T →
          ∀ (μ : K), μ ≠ (0 : K) → μ ≠ (1 : K) → IsCompl (LinearMap.ker T) (LinearMap.range T) :=
      by repeat (sorry)
    sorry
  -/

  theorem is_unit_sub_smul_id_of_is_idempotent_of_ne_zero_of_ne_one :
      ∀ {K : Type u} {V : Type v} [inst : Field K] [inst_1 : AddCommGroup V] [inst_2 : Module K V]
        [FiniteDimensional K V] {T : V →ₗ[K] V},
        T * T = T → ∀ {μ : K}, μ ≠ (0 : K) → μ ≠ (1 : K) → IsUnit (T - μ • (1 : V →ₗ[K] V)) :=
    by
    intro K V inst inst_1 inst_2 inst_7439058897038094550 T hT μ hμ0 hμ1
    have assert_9640271237634751201 :
      ∀ (T : V →ₗ[K] V),
        T * T = T →
          ∀ (μ : K),
            μ ≠ (0 : K) →
              μ ≠ (1 : K) →
                (∀ (v : V), (T : V → V) ((T : V → V) v) = (T : V → V) v) ∧
                  ∀ v ∈ LinearMap.range T, (T : V → V) v = v :=
      by
      repeat (sorry)
    have assert_290240271064752550 :
      ∀ (T : V →ₗ[K] V),
        T ∘ₗ T = T →
          ∀ (μ : K), μ ≠ (0 : K) → μ ≠ (1 : K) → ∀ v ∈ LinearMap.range T, (T : V → V) v = v :=
      by repeat (sorry)
    have assert_11918856549779650521 :
      ∀ (T : V →ₗ[K] V),
        T * T = T →
          ∀ (c : K),
            c ≠ (0 : K) →
              c ≠ (1 : K) →
                ∀ (μ : K),
                  μ ≠ (0 : K) → μ ≠ (1 : K) → ∀ (v : V), v - (T : V → V) v ∈ LinearMap.ker T :=
      by repeat (sorry)
    have assert_5323617169768303690 :
      ∀ (T : V →ₗ[K] V),
        T * T = T → LinearMap.ker T ⊔ LinearMap.range T = ⊤ :=
      by repeat (sorry)
    have assert_3605381847287387093 :
      ∀ (T : V →ₗ[K] V),
        T * T = T →
          ∀ (la mu : K),
            la ≠ (0 : K) →
              la ≠ (1 : K) →
                mu ≠ (0 : K) → mu ≠ (1 : K) → LinearMap.ker T ⊓ LinearMap.range T = ⊥ :=
      by repeat (sorry)
    have assert_10502880745762333757 :
      ∀ (T : V →ₗ[K] V),
        T * T = T →
          ∀ (μ : K), μ ≠ (0 : K) → μ ≠ (1 : K) → IsCompl (LinearMap.ker T) (LinearMap.range T) :=
      by repeat (sorry)
    sorry
