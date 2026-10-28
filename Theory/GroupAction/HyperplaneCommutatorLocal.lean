module

public import Theory.GroupAction.HyperplaneCommutatorGeneration
public import Theory.GroupTheory.Commutator.NormalizesSupplement
public import Theory.GroupTheory.PCoreSurjective.OddExtension
public import Theory.GroupTheory.PResidual.NormalSubgroup
public import Theory.ElementaryAbelian.GeneratorRank

/-!
# The local factors in hyperplane commutator generation

Let X be a normal odd-prime subgroup, let A be elementary abelian of exponent
two, and let R be a two-subgroup containing A and O₂(G) and centralizing A
modulo O₂(G). For a hyperplane B of A set D=[C_X(B),A]. Then R normalizes D,
and D=[D,A]. If D is nontrivial, the image of A in (DR)/O₂(DR) has rank one;
the image of D is its nontrivial full odd-prime core, with two-group quotient.

The ambient two-core centralizes X. Thus adjoining it to A or B does not
change the relevant commutator or relative centralizer. R normalizes these
joins, hence D. The two-subgroup B O₂(G) is normal in DR, so B dies in the
intrinsic two-core quotient. This bounds the actor image by two; full
commutation and the odd order of D show the image is nontrivial.

Source: Aschbacher--Smith, combined manuscript (1 March 2004), proof of
E.1.10(6), printed p.212. The source application takes R=τ(G,T,A).
Trivial factors are deliberately excluded only from the rank-one assertion.
-/

namespace Subgroup
open scoped IsMulCommutative commutatorElement
variable {G : Type*} [Group G]

private theorem commutator_sup_central_right (C A N : Subgroup G) [N.Normal]
    (hCN : C ≤ centralizer (N : Set G)) : ⁅C, A ⊔ N⁆ = ⁅C, A⁆ := by
  apply le_antisymm
  · apply commutator_le.mpr
    intro c hc t ht
    obtain ⟨a, ha, n, hn, rfl⟩ := mem_sup_of_normal_right.mp ht
    have he : ⁅c, n⁆ = 1 := commutatorElement_eq_one_iff_mul_comm.mpr ((hCN hc) n hn).symm
    simpa only [commutatorElement_mul_right_eq_mul_conj, he, mul_one,
      mul_inv_cancel_right] using (commutator_mem_commutator hc ha)
  · exact commutator_mono le_rfl le_sup_left

private theorem normalizes_commutator_of_normalizes (R C A : Subgroup G)
    (hRC : R ≤ normalizer C) (hRA : R ≤ normalizer A) :
    R ≤ normalizer (⁅C,A⁆ : Subgroup G) := by
  intro r hr
  apply mem_normalizer_iff_map_conj_eq.mpr
  rw [map_commutator, mem_normalizer_iff_map_conj_eq.mp (hRC hr),
    mem_normalizer_iff_map_conj_eq.mp (hRA hr)]

private theorem inf_centralizer_sup_of_central (X B N : Subgroup G)
    (hXN : X ≤ centralizer (N : Set G)) :
    X ⊓ centralizer (B ⊔ N : Subgroup G) = X ⊓ centralizer (B : Set G) := by
  have hB : B ≤ B ⊔ N := le_sup_left
  apply le_antisymm (inf_le_inf_left _ (centralizer_le hB))
  apply le_inf inf_le_left
  apply le_centralizer_iff.mpr
  exact sup_le (le_centralizer_iff.mp inf_le_right)
    (le_centralizer_iff.mp (inf_le_left.trans hXN))

private theorem coprime_commutator_idempotent [Finite G]
    (C A : Subgroup G) (hAC : A ≤ normalizer C)
    (hsolv : Group.IsSolvable C) (hcop : Nat.Coprime (Nat.card A) (Nat.card C)) :
    ⁅C,A⁆ = ⁅⁅C,A⁆,A⁆ := by
  let _ : Normalizes A C := ⟨hAC⟩
  have hm := commutatorAction_subgroup_conj_map_eq_commutator C A hAC
  apply le_antisymm
  · calc
      ⁅C,A⁆ = (commutatorAction₂ (A := A) (G := C)).map C.subtype := by
        rw [commutatorAction₂_eq_commutatorAction_of_solvable_coprime hsolv hcop, hm]
      _ ≤ ⁅⁅C,A⁆,A⁆ := ?_
    rw [commutatorAction₂, commutatorSubgroup, MonoidHom.map_closure, closure_le]
    rintro _ ⟨v, ⟨a, c, hc, rfl⟩, rfl⟩
    have hcm : (c : G) ∈ ⁅C,A⁆ := by
      rw [← hm]
      exact mem_map_of_mem _ hc
    change (c : G)⁻¹ * ((a : G) * (c : G) * (a : G)⁻¹) ∈ ⁅⁅C,A⁆,A⁆
    simpa only [commutatorElement_def, inv_inv, mul_assoc] using
      commutator_mem_commutator ((⁅C,A⁆).inv_mem hcm) a.property
  · exact le_normalizer_iff_commutator_le_left.mp (normalizer_commutator_ge_right C A)

variable [Finite G]

/-- Nontrivial hyperplane factors have rank-one actor image after the local two-core quotient. -/
public theorem hyperplane_commutator_local_odd_data
    {p : ℕ} [Fact p.Prime] (hp : p ≠ 2)
    (X A R : Subgroup G) [X.Normal] (hX : IsPGroup p X)
    [IsElementaryAbelian 2 A] (hR : IsPGroup 2 R)
    (hAR : A ≤ R) (hNR : pCore 2 G ≤ R) (hcomm : ⁅A,R⁆ ≤ pCore 2 G)
    (B : Subgroup A) (hB : B.index = 2)
    (hne : ⁅X ⊓ centralizer (B.map A.subtype : Set G), A⁆ ≠ ⊥) :
    let D := ⁅X ⊓ centralizer (B.map A.subtype : Set G), A⁆
    let K := D ⊔ R
    let Q := K ⧸ pCore 2 K
    let a := (A.subgroupOf K).map (QuotientGroup.mk' (pCore 2 K))
    R ≤ normalizer D ∧ D = ⁅D,A⁆ ∧
      IsPGroup 2 (Q ⧸ pCore p Q) ∧ pCore p Q ≠ ⊥ ∧
        pCore p Q = ⁅pCore p Q, a⁆ ∧ Group.rank a = 1 := by
  let N := pCore 2 G
  let b := B.map A.subtype
  let C := X ⊓ centralizer (b : Set G)
  let D := ⁅C,A⁆
  let K := D ⊔ R
  have hbA : b ≤ A := map_subtype_le B
  have hXN : X ≤ centralizer (N : Set G) := by
    apply commutator_eq_bot_iff_le_centralizer.mp
    exact commutator_eq_bot_of_disjoint
      (IsPGroup.disjoint_of_ne p 2 hp X N hX pCore_isPGroup)
  have hRX : R ≤ normalizer X := by rw [normalizer_eq_top]; exact le_top
  have hRbN : R ≤ normalizer (b ⊔ N : Subgroup G) :=
    le_normalizer_sup_of_commutator_le A R b N hbA hcomm
  have hRC : R ≤ normalizer C := by
    rw [show C = X ⊓ centralizer (b ⊔ N : Subgroup G) from
      (inf_centralizer_sup_of_central X b N hXN).symm]
    exact (le_inf hRX (hRbN.trans (normalizer_le_normalizer_centralizer _))).trans
      inf_normalizer_le_normalizer_inf
  have hDle : D ≤ C := le_normalizer_iff_commutator_le_left.mp (hAR.trans hRC)
  have hDX : D ≤ X := hDle.trans inf_le_left
  have hRD : R ≤ normalizer D := by
    rw [show D = ⁅C, A ⊔ N⁆ from
      (commutator_sup_central_right C A N (inf_le_left.trans hXN)).symm]
    exact normalizes_commutator_of_normalizes R C (A ⊔ N) hRC
      (le_normalizer_sup_of_commutator_le A R A N le_rfl hcomm)
  have hpC : IsPGroup p C := hX.of_injective (inclusion inf_le_left) (inclusion_injective _)
  have hDA : D = ⁅D,A⁆ := coprime_commutator_idempotent C A (hAR.trans hRC)
    (@IsNilpotent.to_isSolvable _ _ hpC.isNilpotent)
    (IsPGroup.coprime_card_of_ne 2 p hp.symm A C (IsElementaryAbelian.isPGroup 2 A) hpC)
  have hPcentral : b ⊔ N ≤ centralizer (D : Set G) := by
    apply sup_le
    · exact le_centralizer_iff.mp (hDle.trans inf_le_right)
    · exact le_centralizer_iff.mp (hDX.trans hXN)
  have hKP : K ≤ normalizer (b ⊔ N : Subgroup G) :=
    sup_le ((le_centralizer_iff.mp hPcentral).trans (centralizer_le_normalizer _)) hRbN
  have hPR : b ⊔ N ≤ R := sup_le (hbA.trans hAR) hNR
  have hPcore : (b ⊔ N).subgroupOf K ≤ pCore 2 K := by
    let _ := normal_subgroupOf_of_le_normalizer hKP
    have hP : IsPGroup 2 (b ⊔ N : Subgroup G) :=
      hR.of_injective (inclusion hPR) (inclusion_injective _)
    exact le_sSup ⟨inferInstance, hP.comap_subtype⟩
  have hAK : A ≤ K := hAR.trans le_sup_right
  let q := QuotientGroup.mk' (pCore 2 K)
  let a := (A.subgroupOf K).map q
  let f : A →* K ⧸ pCore 2 K := q.comp (inclusion hAK)
  have hfker : B ≤ f.ker := by
    intro x hx
    apply (QuotientGroup.eq_one_iff _).mpr
    exact hPcore (show (x : G) ∈ b ⊔ N from (show b ≤ b ⊔ N from le_sup_left) (mem_map_of_mem _ hx))
  have hfrange : f.range = a := by
    ext x
    constructor
    · rintro ⟨y, rfl⟩
      exact ⟨inclusion hAK y, y.property, rfl⟩
    · rintro ⟨y, hy, rfl⟩
      exact ⟨⟨y, hy⟩, rfl⟩
  have hacard : Nat.card a ≤ 2 := by
    rw [← hfrange, ← index_ker]
    exact Nat.le_of_dvd (by decide) (by simpa only [hB] using index_dvd_of_le hfker)
  let _ : IsElementaryAbelian 2 (A.subgroupOf K) := IsElementaryAbelian.subgroupOf hAK
  let _ : IsElementaryAbelian 2 a := IsElementaryAbelian.map q
  have hrank : Group.rank a ≤ 1 := IsElementaryAbelian.rank_le_of_card_le (p := 2) a
    (by simpa only [pow_one] using hacard)
  let DK := D.subgroupOf K
  let _ : DK.Normal := normal_subgroupOf_of_le_normalizer (sup_le D.le_normalizer hRD)
  have hDp : IsPGroup p DK := (hX.of_injective (inclusion hDX)
    (inclusion_injective _)).comap_subtype
  have hgen : DK ⊔ R.subgroupOf K = ⊤ := by
    rw [← subgroupOf_sup le_sup_left le_sup_right, subgroupOf_self]
  have hquot : IsPGroup 2 (K ⧸ DK) :=
    isPGroup_quotient_of_sup_eq_top DK (R.subgroupOf K) hR.comap_subtype hgen
  have hDAK : DK = ⁅DK, A.subgroupOf K⁆ := by
    apply map_injective K.subtype_injective
    rw [map_commutator, map_subgroupOf_eq_of_le le_sup_left,
      map_subgroupOf_eq_of_le hAK]
    exact hDA
  have hDne : DK ≠ ⊥ := by
    intro he
    apply hne
    have hm := congrArg (fun H : Subgroup K => H.map K.subtype) he
    rw [show DK.map K.subtype = D from map_subgroupOf_eq_of_le (show D ≤ K from le_sup_left),
      map_bot] at hm
    exact hm
  have hmapne : DK.map q ≠ ⊥ := by
    intro he
    have hle : DK ≤ pCore 2 K := by
      simpa only [map_eq_bot_iff, q, QuotientGroup.ker_mk'] using he
    exact hDne (disjoint_self.mp
      ((IsPGroup.disjoint_of_ne p 2 hp DK (pCore 2 K) hDp pCore_isPGroup).mono_right hle))
  have hmapcomm : DK.map q = ⁅DK.map q, a⁆ := by
    conv_lhs => rw [hDAK]
    exact map_commutator _ _ q
  have hane : a ≠ ⊥ := by
    intro he
    exact hmapne (by simpa only [he, commutator_bot_right] using hmapcomm)
  let _ : Nontrivial a := (nontrivial_iff_ne_bot a).mpr hane
  have hcore := odd_core_mod_twoCore hp DK hDp hquot
  refine ⟨hRD, hDA, ?_, ?_, ?_, ?_⟩
  · exact hcore.2.of_equiv (QuotientGroup.quotientMulEquivOfEq hcore.1.symm)
  · rwa [hcore.1]
  · rwa [hcore.1]
  · exact Nat.le_antisymm hrank (Group.rank_pos (G := a))
end Subgroup
