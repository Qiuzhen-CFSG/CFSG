module

public import Theory.GroupTheory.WeakClosureSetFusion
public import Theory.GroupTheory.GeneralizedThompsonTransfer

/-!
# Burnside fusion and Thompson transfer in §A.1

This module proves all clauses of A.1.35–37 of Aschbacher–Smith,
*The Classification of Quasithin Groups*, combined manuscript of 1 March
2004, printed pp.30–31.

Burnside fusion applies to arbitrary subsets normalized by W, and hence to
elements of the ambient centralizer C_G(W). Thompson transfer detects an
ambient involution outside O²(G) using its absence from an index-two subgroup
of a Sylow subgroup. Generalized transfer uses the actual quotient H/K, where K is
normal only in H, and the fusion of all integer powers of a p-element;
for involutions its own fusion class suffices.

The reusable arguments are Sylow correction in a set normalizer and the
ordinary transfer orbit-product evaluation.
-/

namespace CFSG.Quasithin.ChapterA

variable {G : Type*} [Group G] [Finite G]

/-- A.1.35: the normalizer of a weakly closed subgroup of a Sylow subgroup controls
ambient conjugacy of all subsets normalized by that subgroup. -/
public theorem lemma_A_1_35 {p : ℕ} [Fact p.Prime]
    (T : Sylow p G) (W : Subgroup G) (hWT : W ≤ (T : Subgroup G))
    (hweak : ∀ a : G, W.map (MulAut.conj a).toMonoidHom ≤ (T : Subgroup G) →
      a ∈ Subgroup.normalizer (W : Set G))
    (A B : Set G) (hA : W ≤ Subgroup.normalizer A) (hB : W ≤ Subgroup.normalizer B)
    (a : G) (hab : MulAut.conj a '' A = B) :
    ∃ n ∈ Subgroup.normalizer (W : Set G), MulAut.conj n '' A = B :=
  T.weakly_closed_normalizer_controls_set_fusion W hWT hweak A B hA hB a hab

/-- The element-fusion clause of A.1.35, on the entire ambient centralizer of W. -/
public theorem lemma_A_1_35_elements {p : ℕ} [Fact p.Prime]
    (T : Sylow p G) (W : Subgroup G) (hWT : W ≤ (T : Subgroup G))
    (hweak : ∀ a : G, W.map (MulAut.conj a).toMonoidHom ≤ (T : Subgroup G) →
      a ∈ Subgroup.normalizer (W : Set G))
    {x y : G} (hx : x ∈ Subgroup.centralizer (W : Set G))
    (hy : y ∈ Subgroup.centralizer (W : Set G)) (hxy : IsConj x y) :
    ∃ n ∈ Subgroup.normalizer (W : Set G), n * x * n⁻¹ = y :=
  T.weakly_closed_normalizer_controls_centralizer_fusion W hWT hweak hx hy hxy

/-- A.1.36, Thompson transfer: an ambient involution with no conjugate in an
index-two subgroup of a Sylow two-subgroup lies outside the two-residual. -/
public theorem lemma_A_1_36
    (P : Sylow 2 G) (Q : Subgroup P) (hQ : Q.index = 2)
    (u : G) (hu : orderOf u = 2)
    (hno : ∀ v : P, IsConj u (v : G) → v ∉ Q) :
    u ∉ pResidual 2 G :=
  P.involution_not_mem_twoResidual_of_no_conjugate Q hQ u hu hno

/-- A.1.37(1), generalized Thompson transfer. The coset condition is expressed
by `(g ^ m)⁻¹ * x ∈ K`, equivalently `x ∈ g ^ m K`. -/
public theorem lemma_A_1_37_1 {p : ℕ} [Fact p.Prime]
    (H : Subgroup G) (K : Subgroup H) [K.Normal] [IsMulCommutative (H ⧸ K)]
    (hindex : Nat.Coprime p H.index) (g : H)
    (hg : ∃ n : ℕ, orderOf g = p ^ n) (hgK : g ∉ K)
    (hfusion : ∀ (m : ℤ) (x : H),
      IsConj (((g ^ m) : H) : G) (x : G) → (g ^ m)⁻¹ * x ∈ K) :
    (g : G) ∉ _root_.commutator G :=
  Subgroup.not_mem_commutator_of_conjugate_zpowers (G := G) K g hindex hg hgK hfusion

/-- A.1.37(2): for an involution it suffices to check fusion of the involution
itself into H. -/
public theorem lemma_A_1_37_2
    (H : Subgroup G) (K : Subgroup H) [K.Normal] [IsMulCommutative (H ⧸ K)]
    (hindex : Nat.Coprime 2 H.index) (g : H)
    (hg : orderOf g = 2) (hgK : g ∉ K)
    (hfusion : ∀ x : H, IsConj (g : G) (x : G) → g⁻¹ * x ∈ K) :
    (g : G) ∉ _root_.commutator G :=
  Subgroup.not_mem_commutator_of_involution_fusion (G := G) K g hindex hg hgK hfusion

end CFSG.Quasithin.ChapterA
