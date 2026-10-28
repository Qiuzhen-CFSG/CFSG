module
public import CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.CoreCollapse.OppositeCentralizer.ConstructionCore
/-!
# The opposite involution in the parabolic core

The two products ddᵃ and ddᵃ² lie in R: each differs from d² by
an element of [X,L]≤R. Their distinct nontrivial squares exhibit C₄²
inside C_R(w), whose order is already sixteen. This proves
C_R(w)=X∩R≃C₄². Restricting the original parabolic quotient along
I₂=R C_{I₂}(w) supplies the marked S₃ quotient of C_{I₂}(w).

The final construction theorem supplies all these conclusions for one literal
three-factor involution in the original T. The remaining residual centralizer,
local Sylow geometry and global recognition stay with qt-e-14322-core-collapse.
Source: Aschbacher--Smith 14.3.22, printed p.999.
-/

public section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative commutatorElement
namespace CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.CoreCollapse.OppositeCentralizer
open Chapter12.Section08 Chapter12.Section08.InvariantFlag
open Recognition Chapter14.Section02 SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06
variable {G : Type*} [Group G] [Finite G]
variable
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hcard : Nat.card (localModule T M) = 4)
    (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃* Equiv.Perm (Fin 3))
    (hnot : ¬ ClassificationModels.IsTheoremEModel G)
    (F : InvariantFlag T (rankTwoSeed T M) 2)
    [IsElementaryAbelian 2 (rankTwoSeed T M)]
    (hne : ¬ IsMulCommutative F.U)
    (g : G) (hgP : g ∈ F.P (sourceResidual M Mc)) (hgH : g ∉ F.H)
    (hs : Group.IsSolvable F.TerminalHdot)
    (hself : FactorSelfCentralizing F (sourceResidual M Mc))
    (hc : CyclicTIInput F (sourceResidual M Mc)) {z d a : G}
    (s : CubicTriple F (sourceResidual M Mc) z d a)
include hG hempty hM hu hmany hcard e hnot hne hgP hgH hs hself hc s

omit hself s in
private theorem source_span_residual_commutator_le :
    ⁅span F, sourceResidual M Mc⁆ ≤ (F.I₂ (sourceResidual M Mc)).pCoreIn 2 := by
  let L := sourceResidual M Mc
  let h := source_lemma_14_2_4 hG T hempty hM hu hmany hcard e
  have hcore := (source_parabolic_residual_core_structure_of_solvable
    hG T hempty hM hu hmany hcard e hnot F hne g hgP hgH hs).2.2.1
  have hXL : span F ≤ normalizer (L : Set G) :=
    (conjugateSubgroupClosure_le_self _ _).trans h.sylow_normalizes_L
  have hLX : L ≤ normalizer (span F : Set G) := le_sup_left.trans hc.normalized
  have hnorm : L ≤ normalizer ((span F ⊓ L : Subgroup G) : Set G) :=
    (le_inf hLX L.le_normalizer).trans inf_normalizer_le_normalizer_inf
  have htwo : IsPGroup 2 (span F ⊓ L : Subgroup G) :=
    T.isPGroup'.to_le (inf_le_left.trans (conjugateSubgroupClosure_le_self _ _))
  have hle := le_pCoreIn_of_normalizes htwo inf_le_right hnorm
  rw [hcore] at hle
  exact (le_inf (le_normalizer_iff_commutator_le_left.mp hLX)
    (le_normalizer_iff_commutator_le_right.mp hXL)).trans hle

/-- The two explicit products of cyclic generators identify the literal core centralizer. -/
theorem source_triple_core_centralizer :
    (F.I₂ (sourceResidual M Mc)).pCoreIn 2 ⊓ centralizer ({tripleProduct d a} : Set G) =
      span F ⊓ (F.I₂ (sourceResidual M Mc)).pCoreIn 2 ∧
    Nonempty (((F.I₂ (sourceResidual M Mc)).pCoreIn 2 ⊓
      centralizer ({tripleProduct d a} : Set G) : Subgroup G) ≃*
      (Multiplicative (ZMod 4) × Multiplicative (ZMod 4))) := by
  let X := span F
  let R := (F.I₂ (sourceResidual M Mc)).pCoreIn 2
  let C := R ⊓ centralizer ({tripleProduct d a} : Set G)
  let := hc.abelian
  have hcc (x y : G) (hx : x ∈ X) (hy : y ∈ X) : Commute x y :=
    congrArg Subtype.val (mul_comm' (⟨x,hx⟩ : X) ⟨y,hy⟩)
  obtain ⟨h0,h1,h2⟩ := s.factors_mem_span hc
  have hCX : X ⊓ R ≤ C := by
    intro x hx
    exact ⟨hx.2, mem_centralizer_singleton_iff.mpr (hcc x _ hx.1 (s.product_mem_span hc))⟩
  have hbound := source_span_residual_commutator_le hG T hempty hM hu hmany hcard e hnot F hne g hgP hgH hs hc
  have hprod (b : G) (hb : b ∈ sourceResidual M Mc) : d * (MulAut.conj b⁻¹) d ∈ R := by
    have hd2 : d ^ 2 ∈ R := s.square.symm ▸
      (s.seed_le_core (F.le_seed 1 (s.point.symm ▸ mem_zpowers z)))
    have hdR := hbound (commutator_mem_commutator (X.inv_mem h0) ((sourceResidual M Mc).inv_mem hb))
    have he : d * (MulAut.conj b⁻¹) d = d ^ 2 * ⁅d⁻¹,b⁻¹⁆ := by
      simp only [MulAut.conj_apply, commutatorElement_def, inv_inv, pow_two]
      group
    exact he.symm ▸ R.mul_mem hd2 hdR
  let x := d * (MulAut.conj a⁻¹) d
  let y := d * (MulAut.conj (a ^ 2)⁻¹) d
  have hxR : x ∈ R := hprod a s.actor_mem
  have hyR : y ∈ R := hprod (a ^ 2) ((sourceResidual M Mc).pow_mem s.actor_mem 2)
  have hxX : x ∈ X := X.mul_mem h0 h1
  have hyX : y ∈ X := X.mul_mem h0 h2
  have hxC : x ∈ C := hCX ⟨hxX,hxR⟩
  have hyC : y ∈ C := hCX ⟨hyX,hyR⟩
  have hx2 : x ^ 2 = z * (MulAut.conj a⁻¹) z := by
    rw [(hcc _ _ h0 h1).mul_pow, ← map_pow, s.square]
  have hy2 : y ^ 2 = z * (MulAut.conj (a ^ 2)⁻¹) z := by
    rw [(hcc _ _ h0 h2).mul_pow, ← map_pow, s.square]
  have hzV : z ∈ rankTwoSeed T M := F.le_seed 1 (s.point.symm ▸ mem_zpowers z)
  have hz2 : z ^ 2 = 1 := elemPow_eq_one_of_isElementaryAbelian z hzV
  have hzInv : z⁻¹ = z := inv_eq_of_mul_eq_one_left (by simpa only [pow_two] using hz2)
  have hxNe : x ^ 2 ≠ 1 := by
    rw [hx2]
    intro hh
    exact s.squares_distinct.1 ((eq_inv_of_mul_eq_one_left hh).trans (by rw [← map_inv,hzInv]))
  have hyNe : y ^ 2 ≠ 1 := by
    rw [hy2]
    intro hh
    exact s.squares_distinct.2.1 ((eq_inv_of_mul_eq_one_left hh).trans (by rw [← map_inv,hzInv]))
  have hdistinct : x ^ 2 ≠ y ^ 2 := by
    rw [hx2,hy2]
    exact fun hh => s.squares_distinct.2.2 (mul_left_cancel hh)
  have hd4 : d ^ 4 = 1 := by
    have hd := congrArg (fun k : G => k ^ 2) s.square
    rw [← pow_mul, hz2] at hd
    exact hd
  have hx4 : x ^ 4 = 1 := by
    rw [(hcc _ _ h0 h1).mul_pow, ← map_pow, hd4, map_one, one_mul]
  have hy4 : y ^ 4 = 1 := by
    rw [(hcc _ _ h0 h2).mul_pow, ← map_pow, hd4, map_one, one_mul]
  have hcardC : Nat.card C = 16 := (source_triple_core_orbit_and_card
    hG T hempty hM hu hmany hcard e hnot F hne g hgP hgH hs hself hc s).2
  have hmodel : Nonempty (C ≃* (Multiplicative (ZMod 4) × Multiplicative (ZMod 4))) := by
    apply nonempty_mulEquiv_c4_square_of_independent_roots hcardC (⟨x,hxC⟩ : C) ⟨y,hyC⟩
    · exact Subtype.ext hx4
    · exact Subtype.ext hy4
    · exact fun hh => hxNe (congrArg Subtype.val hh)
    · exact fun hh => hyNe (congrArg Subtype.val hh)
    · exact fun hh => hdistinct (congrArg Subtype.val hh)
    · exact Subtype.ext (hcc _ _ hxX hyX).eq
  have hcardXR : 16 ≤ Nat.card (X ⊓ R : Subgroup G) := by
    have hxO : orderOf x = 4 := orderOf_eq_four_of_fourth_power hx4 hxNe
    have hyO : orderOf y = 4 := orderOf_eq_four_of_fourth_power hy4 hyNe
    have hxy : zpowers x ≤ centralizer (zpowers y : Set G) := by
      rintro u ⟨i,rfl⟩ v ⟨j,rfl⟩
      exact ((hcc x y hxX hyX).zpow_zpow i j).symm.eq
    obtain ⟨q,_⟩ := exists_mulEquiv_prod_sup_of_disjoint_of_commuting
      (zpowers x) (zpowers y) (disjoint_zpowers_of_order_four_distinct_squares hxO hyO hdistinct) hxy
    have hcardP : Nat.card (zpowers x ⊔ zpowers y : Subgroup G) = 16 := by
      rw [← Nat.card_congr q.toEquiv, Nat.card_prod, Nat.card_zpowers, Nat.card_zpowers, hxO,hyO]
    exact hcardP ▸ card_le_of_le (sup_le (zpowers_le.mpr ⟨hxX,hxR⟩) (zpowers_le.mpr ⟨hyX,hyR⟩))
  exact ⟨(eq_of_le_of_card_ge hCX (hcardC ▸ hcardXR)).symm,hmodel⟩

/-- Restriction of the original parabolic S₃ quotient preserves its literal core kernel. -/
theorem source_triple_parabolic_quotient :
    ∃ q : (F.I₂ (sourceResidual M Mc) ⊓ centralizer ({tripleProduct d a} : Set G) : Subgroup G) →*
      Equiv.Perm (Fin 3), Function.Surjective q ∧
      q.ker = ((F.I₂ (sourceResidual M Mc)).pCoreIn 2).subgroupOf
        (F.I₂ (sourceResidual M Mc) ⊓ centralizer ({tripleProduct d a} : Set G)) := by
  let h := source_lemma_14_2_4 hG T hempty hM hu hmany hcard e
  have dg := rankTwo_closure_geometry h F hne
  let : Fact (IsPGroup 2 F.U) := ⟨dg.two⟩
  have hPhi : (frattini F.U).map F.U.subtype = F.Vi 1 := by
    rw [dg.frattini_point]
    exact map_subgroupOf_eq_of_le ((F.le_seed 1).trans (le_conjugateSpanBy _ _))
  have hcomm : ⁅F.U,F.U⁆ ≤ F.Vi 1 := by
    rw [← F.U.map_subtype_commutator]
    exact (map_mono (f := F.U.subtype) (commutator_le_frattini_of_isPGroup (p := 2))).trans hPhi.le
  have hsquare : ∀ u ∈ F.U, u ^ 2 ∈ F.Vi 1 := fun u hu =>
    hPhi ▸ mem_map_of_mem F.U.subtype (pth_power_mem_frattini_of_isPGroup (p := 2) (⟨u,hu⟩ : F.U))
  have hspan : F.U = conjugateSpanBy (F.Vi 2) F.H := by rw [F.last]; rfl
  obtain ⟨eI, _⟩ := F.binary_generation (by decide) (sourceResidual M Mc)
    h.L_normalizes_seed (h.binarySeedAction_surjective F) h.centralizer hcomm hsquare hspan hne g hgP hgH
  let I := F.I₂ (sourceResidual M Mc)
  let C := I ⊓ centralizer ({tripleProduct d a} : Set G)
  let q : I →* Equiv.Perm (Fin 3) := eI.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 I))
  have hq : Function.Surjective q := eI.surjective.comp (QuotientGroup.mk'_surjective _)
  have hk : q.ker = pCore 2 I := by
    rw [MonoidHom.ker_comp_of_injective _ _ eI.injective, QuotientGroup.ker_mk']
  let j : C →* I := inclusion inf_le_left
  have hjoin : pCore 2 I ⊔ C.subgroupOf I = ⊤ := by
    apply map_injective I.subtype_injective
    rw [Subgroup.map_sup, map_subgroupOf_eq_of_le (show C ≤ I from inf_le_left),
      ← MonoidHom.range_eq_map, range_subtype]
    exact (source_triple_parabolic_frattini hG T hempty hM hu hmany hcard e hnot F hne g hgP hgH hs hself hc s).symm
  have hj : j.range = C.subgroupOf I := inclusion_range inf_le_left
  have hsurj : Function.Surjective (q.comp j) := by
    apply MonoidHom.range_eq_top.mp
    rw [MonoidHom.range_comp, hj]
    have hh := congrArg (Subgroup.map q) hjoin
    rw [← hk, Subgroup.map_sup, Subgroup.map_ker_self, bot_sup_eq, map_top_of_surjective q hq] at hh
    exact hh
  refine ⟨q.comp j, hsurj, ?_⟩
  ext x
  change q (j x) = 1 ↔ (x : G) ∈ I.pCoreIn 2
  rw [← MonoidHom.mem_ker, hk]
  constructor
  · intro hx
    exact mem_map_of_mem I.subtype hx
  · rintro ⟨y,hy,he⟩
    have hey : y = j x := Subtype.ext he
    exact hey ▸ hy

omit hc s in
/-- One literal opposite involution supplies the core displacement, centralizer,
parabolic Frattini factorization and marked S₃ quotient. These are the
corresponding clauses of 14.3.22, not the outstanding global recognition. -/
theorem source_opposite_parabolic_geometry (hproper : F.Vi 1 < supplement F) :
    ∃ z d a : G, CubicTriple F (sourceResidual M Mc) z d a ∧
      tripleProduct d a ∈ (T : Subgroup G) ∧ orderOf (tripleProduct d a) = 2 ∧
      ¬ IsConj z (tripleProduct d a) ∧
      IsConj (tripleProduct d a) (tripleProduct d a * z) ∧
      ⁅(F.I₂ (sourceResidual M Mc)).pCoreIn 2, zpowers (tripleProduct d a)⁆ = rankTwoSeed T M ∧
      (F.I₂ (sourceResidual M Mc)).pCoreIn 2 ⊓ centralizer ({tripleProduct d a} : Set G) =
        span F ⊓ (F.I₂ (sourceResidual M Mc)).pCoreIn 2 ∧
      Nonempty (((F.I₂ (sourceResidual M Mc)).pCoreIn 2 ⊓
        centralizer ({tripleProduct d a} : Set G) : Subgroup G) ≃*
        (Multiplicative (ZMod 4) × Multiplicative (ZMod 4))) ∧
      F.I₂ (sourceResidual M Mc) = (F.I₂ (sourceResidual M Mc)).pCoreIn 2 ⊔
        (F.I₂ (sourceResidual M Mc) ⊓ centralizer ({tripleProduct d a} : Set G)) ∧
      ∃ q : (F.I₂ (sourceResidual M Mc) ⊓ centralizer ({tripleProduct d a} : Set G) : Subgroup G) →*
        Equiv.Perm (Fin 3), Function.Surjective q ∧
        q.ker = ((F.I₂ (sourceResidual M Mc)).pCoreIn 2).subgroupOf
          (F.I₂ (sourceResidual M Mc) ⊓ centralizer ({tripleProduct d a} : Set G)) := by
  have hc := source_cyclicTIInput
    hG T hempty hM hu hmany hcard e hnot F hne g hgP hgH hs hself hproper
  obtain ⟨z, d, a, s, hwT, hw⟩ := source_triple_involution
    hG T hempty hM hu hmany hcard e hnot F hne g hgP hgH hs hc
  obtain ⟨hcentralizer, hmodel⟩ := source_triple_core_centralizer
    hG T hempty hM hu hmany hcard e hnot F hne g hgP hgH hs hself hc s
  exact ⟨z, d, a, s, hwT, hw,
    source_triple_nonfusion hG T hempty hM hu hmany hcard e hnot F hne g hgP hgH hs hself hc s,
    source_triple_product_fusion hG T hempty hM hu hmany hcard e hnot F hne g hgP hgH hs hself hc s,
    source_triple_core_commutator hG T hempty hM hu hmany hcard e hnot F hne g hgP hgH hs hself hc s,
    hcentralizer, hmodel,
    source_triple_parabolic_frattini hG T hempty hM hu hmany hcard e hnot F hne g hgP hgH hs hself hc s,
    source_triple_parabolic_quotient hG T hempty hM hu hmany hcard e hnot F hne g hgP hgH hs hself hc s⟩

end CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.CoreCollapse.OppositeCentralizer
