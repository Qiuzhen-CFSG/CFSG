module
public import CFSG.Quasithin.Chapter15.Section03.Nonabelian.Fusion.Source50.PairGeometry.FactorPermutation
public import Theory.ElementaryAbelian.Extraspecial
public import Theory.Frattini.PGroup
public import Theory.GroupTheory.DisjointConjugateCenter

/-!
# The centers and extraspecial closure in 15.3.55

For the literal closure U and pair P, the G.2.6 action identifies Z(U) ∩ V
with the singular point Z and forces Z(U) into the marked subgroup W.
On the abelian group Z(P), the two residual factors give successive coprime
splittings. Their double commutator is V, so their fixed subgroups form a
canonical complement to V. Conjugation by T permutes the factors and preserves
this complement; the omega-center condition makes it trivial. Consequently
Z(P) = V and Z(U) = Z, and the Frattini bound proves U extraspecial.

The exported literal theorem uses the actual subgroup centers and inclusions.
Source: Aschbacher–Smith, Lemma 15.3.55, printed pp.1146–1147.
-/

@[expose] public noncomputable section
open Subgroup
open CFSG.Quasithin.Chapter15.Section03.Nonabelian
open CFSG.Quasithin.ChapterG.Section02.OrthogonalPlusFour.Chapter15Collapse

namespace CFSG.Quasithin.Chapter15.Section03.Nonabelian.Fusion.Source50.PairGeometry
variable {G : Type*} [Group G] [Finite G]

private theorem centerP_of_split (T P V C : Subgroup G)
    (hT : IsPGroup 2 T) (hPT : P ≤ T)
    (hcenter : centerIn P = V ⊔ C)
    (hVC : Disjoint C V) (hTC : T ≤ normalizer (C : Set G))
    (hOmega : omegaCenter T ≤ V) :
    centerIn P = V := by
  have hCT : C ≤ T := le_sup_right.trans (hcenter.symm.le.trans
    ((show centerIn P ≤ P from inf_le_left).trans hPT))
  have hC : C = ⊥ := normal_disjoint_omega_eq_bot T C V hT hCT hTC hOmega hVC
  simpa [hC] using hcenter

omit [Finite G] in
private theorem centerU_le_centerP (U P W Wg Ug : Subgroup G)
    (hW : W ≤ U) (hWg : Wg ≤ Ug)
    (hP : P = W ⊔ Wg)
    (hZU : centerIn U ≤ W)
    (hNorm : Wg ≤ normalizer (U : Set G))
    (hPnorm : P ≤ normalizer (Ug : Set G))
    (hdis : centerIn U ⊓ Ug = ⊥) :
    centerIn U ≤ centerIn P := by
  have hZP : centerIn U ≤ P := hZU.trans (le_sup_left.trans hP.symm.le)
  have hZW : centerIn U ≤ centralizer (W : Set G) :=
    (show centerIn U ≤ centralizer (U : Set G) from inf_le_right).trans
      (centralizer_le hW)
  have hcommZ : ⁅centerIn U, Wg⁆ ≤ centerIn U := by
    exact le_normalizer_iff_commutator_le_left.mp (normalizes_centerIn hNorm)
  have hcommUg : ⁅centerIn U, Wg⁆ ≤ Ug := by
    rw [commutator_comm]
    exact (commutator_mono hWg hZP).trans
      (le_normalizer_iff_commutator_le_left.mp hPnorm)
  have hcomm : ⁅centerIn U, Wg⁆ = ⊥ :=
    le_bot_iff.mp (hdis ▸ le_inf hcommZ hcommUg)
  have hZWg : centerIn U ≤ centralizer (Wg : Set G) :=
    commutator_eq_bot_iff_le_centralizer.mp hcomm
  have hZPC : centerIn U ≤ centralizer (P : Set G) := by
    rw [hP]
    apply le_centralizer_iff.mpr
    exact sup_le (le_centralizer_iff.mp hZW) (le_centralizer_iff.mp hZWg)
  exact le_inf hZP hZPC

omit [Finite G] in
private theorem centerU_cross_bot (U Ug V Z : Subgroup G)
    (hinter : U ⊓ Ug ≤ V) (hcenterV : centerIn U ⊓ V = Z)
    (hZUg : Z ⊓ Ug = ⊥) :
    centerIn U ⊓ Ug = ⊥ := by
  apply le_antisymm _ bot_le
  have hU : centerIn U ≤ U := inf_le_left
  have hleV : centerIn U ⊓ Ug ≤ V :=
    (inf_le_inf_right Ug hU).trans hinter
  have hleZ : centerIn U ⊓ Ug ≤ Z := hcenterV ▸ le_inf inf_le_left hleV
  exact hZUg ▸ le_inf hleZ inf_le_right

private theorem extraspecial_of_center (U Z : Subgroup G)
    (hU : IsPGroup 2 U) (hPhi : (frattini U).map U.subtype ≤ Z)
    (hcard : Nat.card Z = 2) (hcenter : centerIn U = Z)
    (hnon : ¬ IsMulCommutative U) :
    IsExtraspecial 2 U ∧ center U = Z.subgroupOf U := by
  let : Fact (IsPGroup 2 U) := ⟨hU⟩
  have hc : (center U).map U.subtype = Z := (centerIn_eq_map_center U).symm.trans hcenter
  have hc' : center U = Z.subgroupOf U := by
    rw [← hc, subgroupOf_map_subtype_eq]
  have hPhiC : frattini U ≤ center U := by
    intro x hx
    have hxZ : (x : G) ∈ Z := hPhi (mem_map_of_mem U.subtype hx)
    exact hc'.symm ▸ hxZ
  have hcardC : Nat.card (center U) = 2 := by
    rw [← card_map_of_injective U.subtype_injective, hc, hcard]
  have hquot : IsElementaryAbelian 2 (U ⧸ center U) := {
    toIsMulCommutative :=
      (Subgroup.Normal.quotient_commutative_iff_commutator_le (N := center U)).mpr
        ((commutator_le_frattini_of_isPGroup (p := 2)).trans hPhiC)
    exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr (by
      intro q
      induction q using QuotientGroup.induction_on with
      | H x =>
        change (QuotientGroup.mk' (center U) x) ^ 2 = 1
        rw [← map_pow]
        exact (QuotientGroup.eq_one_iff _).mpr
          (hPhiC (pth_power_mem_frattini_of_isPGroup (p := 2) x))) }
  exact ⟨⟨hcardC, hquot, QuotientGroup.nontrivial_iff.mpr
    (fun h => hnon (center_eq_top_iff.mp h))⟩, hc'⟩

end CFSG.Quasithin.Chapter15.Section03.Nonabelian.Fusion.Source50.PairGeometry

open Subgroup
open CFSG.Quasithin.ChapterG.Section02.OrthogonalPlusFour
open ClassicalOrthogonal.FourPlusMatrix
open PrimeFieldTwo.ModuleGeometry

namespace CFSG.Quasithin.Chapter15.Section03.Nonabelian.Fusion.Source50.PairGeometry

private theorem binary_double_perp (z x : V)
    (h : ∀ w : V, pairing z w = 0 → pairing x w = 0) : x = 0 ∨ x = z := by
  have hs : pairing x ∈ Submodule.span (ZMod 2) {pairing z} := by
    have hh := mem_span_of_iInf_ker_le_ker
      (L := fun _ : Unit => pairing z) (K := pairing x) (by
        simp only [iInf_const]
        exact fun w hw => h w hw)
    simpa using hh
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hs
  have hx : c • z = x := by
    apply sub_eq_zero.mp
    apply pairing_nondegenerate
    intro w
    have he := LinearMap.congr_fun hc w
    simpa only [map_sub, map_smul, LinearMap.sub_apply, LinearMap.smul_apply, sub_eq_zero] using he
  have hc01 : c = 0 ∨ c = 1 := by
    fin_cases c
    · exact Or.inl rfl
    · exact Or.inr rfl
  rcases hc01 with rfl | rfl
  · exact Or.inl (by simpa using hx.symm)
  · exact Or.inr (by simpa using hx.symm)

private theorem binary_fixed_of_stabilizer (z x : V) (hz : z ≠ 0) (hd : z.det = 0)
    (h : ∀ a : Actors, matrixAction a z = z → matrixAction a x = x) :
    x = 0 ∨ x = z := by
  apply binary_double_perp z x
  have hp : perp z ≤ perp x := by
    apply perp_le_of_displacements hz hd
    intro a ha w
    change pairing x (matrixAction a w - w) = 0
    rw [map_sub, ← h a ha, pairing_action, h a ha, sub_self]
  exact fun w hw => hp hw

private theorem binary_fix_perp (z : V) (hd : z.det = 0)
    (a : Actors) (h : ∀ x : V, pairing z x = 0 → matrixAction a x = x) : a = 1 := by
  have hfix (x : V) : matrixAction a x = x := by
    have hm : ∀ w : V, pairing z w = 0 → pairing (matrixAction a x - x) w = 0 := by
      intro w hw
      rw [map_sub, LinearMap.sub_apply, ← h w hw, pairing_action, h w hw, sub_self]
    rcases binary_double_perp z (matrixAction a x - x) hm with he | he
    · exact sub_eq_zero.mp he
    · have hax : matrixAction a x = x + z := by
        simpa [add_comm] using (sub_eq_iff_eq_add.mp he)
      have hpair : pairing x z = 0 := by
        rw [pairing, QuadraticMap.polarBilin_apply_apply, QuadraticMap.polar]
        simp only [determinantForm_apply, ← hax, matrixAction_det, hd, sub_self]
      rw [pairing_symm] at hpair
      exact h x hpair
  apply matrixHom_injective
  rw [map_one]
  apply LinearEquiv.ext
  exact hfix

variable {G : Type*} [Group G] [Finite G] {D : CFSG.Quasithin.ChapterG.Section02.Setup G}
  {g : G} (d : Hypothesis D g)
open CFSG.Quasithin.ChapterG.Section02.Setup

private theorem vectorMap_fixed_of_centralizes {u : G} (hu : u ∈ D.U)
    {x : V} (hc : u * d.vectorMap (Multiplicative.ofAdd x) =
      d.vectorMap (Multiplicative.ofAdd x) * u) :
    matrixAction (d.matrixProjection ⟨u, mem_sup_right hu⟩) x = x := by
  apply Multiplicative.ofAdd.injective
  apply d.vectorMap_injective
  rw [d.vectorMap_action, hc, mul_inv_cancel_right]

include d

private theorem center_inf_module : centerIn D.U ⊓ D.VL = D.V₁ := by
  apply le_antisymm
  · intro x hx
    obtain ⟨z, hz⟩ := d.exists_pointVector_ne_zero
    let v : D.VL := ⟨x, hx.2⟩
    have hfixed (a : Actors) (ha : matrixAction a (d.pointVector z) = d.pointVector z) :
        matrixAction a (d.coordinates v).toAdd = (d.coordinates v).toAdd := by
      have hm : a ∈ d.modelImage D.U := d.modelImage_U_eq_pointStabilizer.symm ▸
        (d.mem_pointStabilizer_iff_fix z hz a).mpr ha
      obtain ⟨u, hu, rfl⟩ := hm
      apply vectorMap_fixed_of_centralizes d hu
      rw [ofAdd_toAdd, d.vectorMap_coordinates]
      change (u : G) * x = x * (u : G)
      exact mem_centralizer_iff.mp hx.1.2 (u : G) hu
    rcases binary_fixed_of_stabilizer (d.pointVector z) (d.coordinates v).toAdd hz
      (d.pointVector_det z) hfixed with he | he
    · have hv : v = 1 := by
        apply d.coordinates.injective
        apply Multiplicative.toAdd.injective
        simpa only [map_one, toAdd_one] using he
      have hx1 : x = 1 := congrArg Subtype.val hv
      exact hx1 ▸ D.V₁.one_mem
    · have hxz : x = z := by
        have he' := congrArg (fun w : V => d.vectorMap (Multiplicative.ofAdd w)) he
        simpa only [ofAdd_toAdd, d.vectorMap_coordinates, d.vectorMap_point] using he'
      rw [hxz]
      exact z.property
  · exact le_inf
      (le_inf (d.base.point_le.trans (le_conjugateSpanBy _ _))
        (le_centralizer_iff.mp d.base.U_le_centralizer_point)) (point_le_VL D)

private theorem center_le_mark : centerIn D.U ≤ D.W g := by
  intro u hu
  have ha1 : d.matrixProjection ⟨u, mem_sup_right hu.1⟩ = 1 := by
    obtain ⟨z, hz⟩ := d.exists_pointVector_ne_zero
    apply binary_fix_perp (d.pointVector z) (d.pointVector_det z)
    intro x hx
    have hxV : d.vectorMap (Multiplicative.ofAdd x) ∈ D.V := by
      change x ∈ d.matrixSubspace D.V
      rw [d.matrixSubspace_V z hz]
      exact hx
    apply vectorMap_fixed_of_centralizes d hu.1
    exact (mem_centralizer_iff.mp hu.2 _ ((le_conjugateSpanBy _ _) hxV)).symm
  have hs : starProjection D (D.L ⊔ D.U) d.LU_le_LT ⟨u, mem_sup_right hu.1⟩ = 1 := by
    apply d.model.injective
    change d.matrixProjection ⟨u, mem_sup_right hu.1⟩ = d.model 1
    rw [map_one]
    exact ha1
  have hcore : (⟨u, mem_sup_right hu.1⟩ : (D.L ⊔ D.U : Subgroup G)) ∈
      pCore 2 (D.L ⊔ D.U : Subgroup G) := by
    rw [← d.LU_starProjection_ker]
    exact hs
  refine ⟨hu.1, ?_⟩
  change u ∈ (D.I g).pCoreIn 2
  rw [d.I_eq_LU]
  exact ⟨_, hcore, rfl⟩

end CFSG.Quasithin.Chapter15.Section03.Nonabelian.Fusion.Source50.PairGeometry

namespace CFSG.Quasithin.Chapter15.Section03.Nonabelian.Fusion.Source50.PairGeometry
open CFSG.Quasithin.ChapterG.Section02
open CFSG.Quasithin.ChapterG.Section02.Setup
open CFSG.Quasithin.ChapterG.Section02.OrthogonalPlusFour
variable {G : Type*} [Group G] [Finite G] {D : Setup G} {g : G}

/-- Given the canonical complement, the omega-center condition identifies
the two centers. -/
private theorem source_centers_of_split (d : Hypothesis D g)
    (hOmega : omegaCenter D.T ≤ D.VL)
    (hsplit : ∃ C : Subgroup G, centerIn (D.S g) = D.VL ⊔ C ∧
      Disjoint C D.VL ∧ D.T ≤ normalizer (C : Set G)) :
    centerIn (D.S g) = D.VL ∧ centerIn D.U = D.V₁ := by
  obtain ⟨C, hC, hdis, hTC⟩ := hsplit
  have hCP := centerP_of_split D.T (D.S g) D.VL C d.base.binary_T_isPGroup
    d.S_le_T hC hdis hTC hOmega
  have hinter : D.U ⊓ conjugate D.U g ≤ D.VL :=
    le_sup_right.trans (Chapter15Collapse.source_collapse d hOmega).2.2.2.2.2.le
  have hcross := centerU_cross_bot D.U (conjugate D.U g) D.VL D.V₁ hinter
    (center_inf_module d) d.point_inf_conjugate_U
  have hSUg : D.S g ≤ normalizer (conjugate D.U g : Set G) := by
    have hm := (map_mono (f := (MulAut.conj g⁻¹).toMonoidHom) d.S_normalizes_U).trans
      (D.U.le_normalizer_map (MulAut.conj g⁻¹).toMonoidHom)
    change conjugate (D.S g) g ≤ normalizer (conjugate D.U g : Set G) at hm
    rwa [conjugate_core D g d.g_mem_I] at hm
  have hWgP : conjugate (D.W g) g ≤ D.S g := by
    rw [conjugate_W D g d.g_mem_I]
    exact inf_le_right
  have hZP := centerU_le_centerP D.U (D.S g) (D.W g) (conjugate (D.W g) g)
    (conjugate D.U g) inf_le_left (map_mono (show D.W g ≤ D.U from inf_le_left))
    d.S_eq_coreProduct (center_le_mark d) (hWgP.trans d.S_normalizes_U) hSUg hcross
  have hZV : centerIn D.U ≤ D.VL := hZP.trans hCP.le
  refine ⟨hCP, ?_⟩
  simpa only [inf_eq_left.mpr hZV] using center_inf_module d

/-- The nonabelian closure and the exact embedded center are consequences
of the source point-stabilizer geometry and the center split. -/
private theorem source_extraspecial_of_split (d : Hypothesis D g)
    (hOmega : omegaCenter D.T ≤ D.VL)
    (hsplit : ∃ C : Subgroup G, centerIn (D.S g) = D.VL ⊔ C ∧
      Disjoint C D.VL ∧ D.T ≤ normalizer (C : Set G)) :
    IsExtraspecial 2 D.U ∧ center D.U = D.V₁.subgroupOf D.U ∧
      D.VL = (center (D.S g)).map (D.S g).subtype := by
  obtain ⟨hCP, hCU⟩ := source_centers_of_split d hOmega hsplit
  have hnon : ¬ IsMulCommutative D.U := by
    intro hc
    let := hc
    have htop : center D.U = ⊤ := center_eq_top
    have hUZ : D.U = D.V₁ := by
      rw [centerIn_eq_map_center, htop, ← MonoidHom.range_eq_map, range_subtype] at hCU
      exact hCU
    have hcard : Nat.card D.V ≤ Nat.card D.V₁ := Nat.card_le_card_of_injective
      (inclusion ((le_conjugateSpanBy D.V D.H).trans hUZ.le)) (inclusion_injective _)
    rw [d.V_card, d.point_card] at hcard
    omega
  obtain ⟨hE, hcenter⟩ := extraspecial_of_center D.U D.V₁
    (U_isPGroup d.base d.closure) d.closure.frattini d.point_card hCU hnon
  exact ⟨hE, hcenter, by simpa only [centerIn_eq_map_center] using hCP.symm⟩

end CFSG.Quasithin.Chapter15.Section03.Nonabelian.Fusion.Source50.PairGeometry

open Subgroup
open scoped Pointwise IsMulCommutative
open CFSG.Quasithin.ChapterG.Section02.OrthogonalPlusFour.Chapter15Collapse

namespace CFSG.Quasithin.Chapter15.Section03.Nonabelian.Fusion.Source50.PairGeometry
variable {G : Type*} [Group G] [Finite G]

omit [Finite G] in
private theorem normalizes_commutator {X A B : Subgroup G}
    (hXA : X ≤ normalizer (A : Set G)) (hXB : X ≤ normalizer (B : Set G)) :
    X ≤ normalizer (⁅A,B⁆ : Subgroup G) := by
  intro x hx
  rw [mem_normalizer_iff_map_conj_eq, map_commutator,
    mem_normalizer_iff_map_conj_eq.mp (hXA hx),
    mem_normalizer_iff_map_conj_eq.mp (hXB hx)]

omit [Finite G] in
private theorem centralizes_subgroups (A : Subgroup G) [IsMulCommutative A]
    {B C : Subgroup G} (hB : B ≤ A) (hC : C ≤ A) : B ≤ centralizer (C : Set G) := by
  intro b hb c hc
  exact congrArg Subtype.val (mul_comm (⟨c,hC hc⟩ : A) ⟨b,hB hb⟩)

/-- Two coprime decompositions yield the canonical unordered fixed-factor
complement when their double displacement is the lower module. -/
private theorem two_actor_split (T P A V X₁ X₂ : Subgroup G)
    [IsMulCommutative A]
    (hT : IsPGroup 2 T) (hAP : A ≤ P) (hPT : P ≤ T)
    (hcentral : A ≤ centralizer (P : Set G))
    (h₁ : X₁ ≤ normalizer (A : Set G)) (h₂ : X₂ ≤ normalizer (A : Set G))
    (h₁₂ : X₁ ≤ normalizer (X₂ : Set G)) (h₂₁ : X₂ ≤ normalizer (X₁ : Set G))
    (hodd₁ : Odd (P.subgroupOf X₁).index) (hodd₂ : Odd (P.subgroupOf X₂).index)
    (hdouble : ⁅⁅A,X₁⁆,X₂⁆ = V) :
    A = V ⊔ ((A ⊓ centralizer (X₁ : Set G)) ⊔ (A ⊓ centralizer (X₂ : Set G))) ∧
      Disjoint V ((A ⊓ centralizer (X₁ : Set G)) ⊔ (A ⊓ centralizer (X₂ : Set G))) := by
  let B := ⁅A,X₁⁆
  let C₁ := A ⊓ centralizer (X₁ : Set G)
  let C₂ := A ⊓ centralizer (X₂ : Set G)
  let C₁₂ := B ⊓ centralizer (X₂ : Set G)
  change ⁅B,X₂⁆ = V at hdouble
  have hBA : B ≤ A := le_normalizer_iff_commutator_le_left.mp h₁
  have hC₁A : C₁ ≤ A := inf_le_left
  have hC₂A : C₂ ≤ A := inf_le_left
  have hC₁₂B : C₁₂ ≤ B := inf_le_left
  have hC₁₂A : C₁₂ ≤ A := hC₁₂B.trans hBA
  have h₂B : X₂ ≤ normalizer (B : Set G) := normalizes_commutator h₂ h₂₁
  have h₁C₂ : X₁ ≤ normalizer (C₂ : Set G) :=
    (le_inf h₁ (h₁₂.trans (normalizer_le_normalizer_centralizer X₂))).trans
      inf_normalizer_le_normalizer_inf
  have coprime {D X : Subgroup G} (hDA : D ≤ A)
      (hn : X ≤ normalizer (D : Set G)) (ho : Odd (P.subgroupOf X).index) :
      Nat.Coprime (Nat.card (D.normalizerMonoidHom.comp (inclusion hn)).range) (Nat.card D) :=
    coprime_conjugation_image D X P hn (hT.to_le (hDA.trans (hAP.trans hPT)))
      (hDA.trans hcentral) ho
  let : IsMulCommutative B := le_centralizer_iff_isMulCommutative.mp
    (centralizes_subgroups A hBA hBA)
  let : IsMulCommutative C₂ := le_centralizer_iff_isMulCommutative.mp
    (centralizes_subgroups A hC₂A hC₂A)
  have hs₁ : B ⊔ C₁ = A ∧ B ⊓ C₁ = ⊥ :=
    commutator_centralizer_decomposition_of_coprime_image A X₁ h₁ (coprime le_rfl h₁ hodd₁)
  have hs₂ : V ⊔ C₁₂ = B ∧ V ⊓ C₁₂ = ⊥ := by
    simpa only [hdouble] using
      commutator_centralizer_decomposition_of_coprime_image B X₂ h₂B (coprime hBA h₂B hodd₂)
  have hsC₂ := commutator_centralizer_decomposition_of_coprime_image C₂ X₁ h₁C₂
    (coprime hC₂A h₁C₂ hodd₁)
  have hC₂ : C₂ ≤ C₁₂ ⊔ C₁ := by
    rw [← hsC₂.1]
    apply sup_le
    · exact (le_inf (commutator_mono hC₂A le_rfl)
        ((le_normalizer_iff_commutator_le_left.mp h₁C₂).trans inf_le_right)).trans le_sup_left
    · exact (le_inf (inf_le_left.trans hC₂A) inf_le_right).trans le_sup_right
  have hCeq : C₁₂ ⊔ C₁ = C₁ ⊔ C₂ := le_antisymm
    (sup_le ((le_inf hC₁₂A inf_le_right).trans le_sup_right) le_sup_left)
    (sup_le le_sup_right hC₂)
  have hVC : V ⊔ (C₁₂ ⊔ C₁) = A := by rw [← sup_assoc, hs₂.1, hs₁.1]
  have hVB : V ≤ B := le_sup_left.trans hs₂.1.le
  have hdis : Disjoint V (C₁₂ ⊔ C₁) := by
    apply disjoint_iff.mpr
    apply eq_bot_iff.mpr
    intro v hv
    have hp : v ∈ (C₁₂ : Set G) * (C₁ : Set G) := by
      rw [← coe_mul_of_left_le_normalizer_right C₁₂ C₁
        ((centralizes_subgroups A hC₁₂A hC₁A).trans (Subgroup.centralizer_le_normalizer _))]
      exact hv.2
    obtain ⟨b, hb, c, hc, he⟩ := hp
    have hcB : c ∈ B := by
      have hm := B.mul_mem (B.inv_mem (hC₁₂B hb)) (hVB hv.1)
      simpa only [← he, inv_mul_cancel_left] using hm
    have hc1 : c = 1 := hs₁.2.le ⟨hcB,hc⟩
    have hvb : v = b := by simpa only [hc1,mul_one] using he.symm
    exact hs₂.2.le ⟨hv.1, hvb.symm ▸ hb⟩
  exact ⟨by rw [← hCeq]; exact hVC.symm, by rwa [← hCeq]⟩

omit [Finite G] in
/-- The sum of the two fixed subgroups is invariant under a group that
permutes the acting factors. -/
private theorem fixed_sum_normalized (T A X₁ X₂ : Subgroup G)
    (hTA : T ≤ normalizer (A : Set G))
    (hperm : ∀ t ∈ T,
      (X₁.map (MulAut.conj t).toMonoidHom = X₁ ∧
        X₂.map (MulAut.conj t).toMonoidHom = X₂) ∨
      (X₁.map (MulAut.conj t).toMonoidHom = X₂ ∧
        X₂.map (MulAut.conj t).toMonoidHom = X₁)) :
    T ≤ normalizer ((A ⊓ centralizer (X₁ : Set G)) ⊔
      (A ⊓ centralizer (X₂ : Set G)) : Subgroup G) := by
  apply le_normalizer_iff.mpr
  intro t ht x hx
  let f := (MulAut.conj t).toMonoidHom
  have hA : A.map f = A := mem_normalizer_iff_map_conj_eq.mp (hTA ht)
  have hfixed (X : Subgroup G) :
      (A ⊓ centralizer (X : Set G)).map f ≤ A ⊓ centralizer (X.map f : Set G) := by
    rw [map_inf _ _ _ (MulAut.conj t).injective, hA]
    exact inf_le_inf_left A (map_centralizer_le_centralizer_image (X : Set G) f)
  have hm : x ∈ (A ⊓ centralizer (X₁ : Set G)) ⊔
      (A ⊓ centralizer (X₂ : Set G)) := hx
  have hm' := mem_map_of_mem f hm
  rw [Subgroup.map_sup] at hm'
  have hle : (A ⊓ centralizer (X₁ : Set G)).map f ⊔
      (A ⊓ centralizer (X₂ : Set G)).map f ≤
      (A ⊓ centralizer (X₁ : Set G)) ⊔ (A ⊓ centralizer (X₂ : Set G)) := by
    rcases hperm t ht with ⟨h₁,h₂⟩ | ⟨h₁,h₂⟩
    · apply sup_le_sup
      · simpa only [f, h₁] using hfixed X₁
      · simpa only [f, h₂] using hfixed X₂
    · apply sup_le
      · have hh : (A ⊓ centralizer (X₁ : Set G)).map f ≤ A ⊓ centralizer (X₂ : Set G) := by
          simpa only [f, h₁] using hfixed X₁
        exact hh.trans le_sup_right
      · have hh : (A ⊓ centralizer (X₂ : Set G)).map f ≤ A ⊓ centralizer (X₁ : Set G) := by
          simpa only [f, h₂] using hfixed X₂
        exact hh.trans le_sup_left
  exact hle hm'

end CFSG.Quasithin.Chapter15.Section03.Nonabelian.Fusion.Source50.PairGeometry

open Subgroup InvertedCubicTensor
open scoped IsMulCommutative
open Representation.BinaryOffender Representation.BinaryQuadraticPair
open ClassicalOrthogonal.FourPlusMatrix
open CFSG.Quasithin.ChapterG.Section02
open CFSG.Quasithin.ChapterG.Section02.Setup
open CFSG.Quasithin.ChapterG.Section02.OrthogonalPlusFour
open CFSG.Quasithin.ChapterG.Section02.OrthogonalPlusFour.Chapter15Collapse

namespace CFSG.Quasithin.Chapter15.Section03.Nonabelian.Fusion.Source50.PairGeometry
variable {G : Type*} [Group G] [Finite G] {D : Setup G} {g : G} (d : Hypothesis D g)
include d

private theorem quotientProjection_eq_one_of_centralizes (x : D.I g)
    (hx : (x : G) ∈ centralizer (D.VL : Set G)) :
    moduleProjection d.quotientSymmetricEquiv x = 1 := by
  have hmatrix : d.quotientMatrixEquiv (QuotientGroup.mk' (pCore 2 (D.I g)) x) = 1 := by
    apply matrixHom_injective
    rw [map_one]
    apply LinearEquiv.ext
    intro m
    change matrixAction (d.quotientMatrixEquiv (QuotientGroup.mk' (pCore 2 (D.I g)) x)) m = m
    have he := d.quotientMatrixEquiv_equivariant x
      (d.coordinates.symm (Multiplicative.ofAdd m))
    have hc := mem_centralizer_iff.mp hx
      (d.coordinates.symm (Multiplicative.ofAdd m))
      (d.coordinates.symm (Multiplicative.ofAdd m)).property
    rw [← hc, mul_inv_cancel_right] at he
    apply Multiplicative.ofAdd.injective
    apply d.coordinates.symm.injective
    apply Subtype.ext
    simpa only [MulEquiv.apply_symm_apply, toAdd_ofAdd] using he
  have hq : QuotientGroup.mk' (pCore 2 (D.I g)) x = 1 :=
    d.quotientMatrixEquiv.injective (hmatrix.trans d.quotientMatrixEquiv.map_one.symm)
  simp only [moduleProjection, MonoidHom.comp_apply, hq, map_one]

private theorem natural_commutator_eq_of_image {X : Subgroup G}
    (hXI : X ≤ D.I g) (hIX : D.I g ≤ normalizer (X : Set G))
    (hne : ∃ x : D.I g, (x : G) ∈ X ∧ moduleProjection d.quotientSymmetricEquiv x ≠ 1) :
    ⁅D.VL,X⁆ = D.VL := by
  have hmove : ⁅D.VL,X⁆ ≤ D.VL :=
    le_normalizer_iff_commutator_le_left.mp (hXI.trans d.I_normalizes_VL)
  have hnorm : D.I g ≤ normalizer (⁅D.VL,X⁆ : Subgroup G) := by
    intro x hx
    rw [mem_normalizer_iff_map_conj_eq, map_commutator,
      mem_normalizer_iff_map_conj_eq.mp (d.I_normalizes_VL hx),
      mem_normalizer_iff_map_conj_eq.mp (hIX hx)]
  rcases d.I_on_VL_irreducible ⁅D.VL,X⁆ hmove hnorm with hbot | he
  · obtain ⟨x,hx,hne⟩ := hne
    have hcentral : X ≤ centralizer (D.VL : Set G) :=
      le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp hbot)
    exact False.elim (hne (quotientProjection_eq_one_of_centralizes d x (hcentral hx)))
  · exact he

private theorem I_normalizes_oddFactor (K : Subgroup (S₃ × S₃)) [K.Normal] :
    D.I g ≤ normalizer (oddFactor (moduleProjection d.quotientSymmetricEquiv) D.L K : Set G) := by
  let π := moduleProjection d.quotientSymmetricEquiv
  have hIN : D.I g ≤ normalizer (actorPreimage π K : Set G) := by
    have hh := (K.comap π).le_normalizer_map (D.I g).subtype
    rw [normalizer_eq_top, ← MonoidHom.range_eq_map, range_subtype] at hh
    exact hh
  have hIL : D.I g ≤ normalizer (D.L : Set G) := by
    rw [d.I_eq_LU]
    exact sup_le D.L.le_normalizer (d.closure.normal.1.trans d.base.T_normalizes_L)
  exact ((le_inf hIL hIN).trans inf_normalizer_le_normalizer_inf).trans
    (normalizer_le_normalizer_characteristic_image _ (pResidual 2 _))

private theorem natural_oddFactor_commutators :
    ⁅D.VL, oddFactor (moduleProjection d.quotientSymmetricEquiv) D.L
      ProductDecomposition.leftFactor⁆ = D.VL ∧
    ⁅D.VL, oddFactor (moduleProjection d.quotientSymmetricEquiv) D.L
      ProductDecomposition.rightFactor⁆ = D.VL := by
  let π := moduleProjection d.quotientSymmetricEquiv
  have hl := mem_oddFactor_image_of_cube π D.L (d.I_eq_LU.symm ▸ le_sup_left)
    ProductDecomposition.leftFactor (cubic,1) (by
      dsimp only [π, moduleProjection]
      rw [d.quotientSymmetricEquiv_L_image]
      simp only [ProductDecomposition.leftFactor, mem_inf, mem_prod, mem_top, mem_bot,
        and_true, Equiv.Perm.mem_alternatingGroup]
      decide +kernel) (by decide +kernel)
  have hr := mem_oddFactor_image_of_cube π D.L (d.I_eq_LU.symm ▸ le_sup_left)
    ProductDecomposition.rightFactor (1,cubic) (by
      dsimp only [π, moduleProjection]
      rw [d.quotientSymmetricEquiv_L_image]
      simp only [ProductDecomposition.rightFactor, mem_inf, mem_prod, mem_top, mem_bot,
        and_true, Equiv.Perm.mem_alternatingGroup]
      decide +kernel) (by decide +kernel)
  constructor
  · apply natural_commutator_eq_of_image d
      ((oddFactor_le π D.L _).trans (actorPreimage_le π _))
      (I_normalizes_oddFactor d _)
    obtain ⟨x,hx,he⟩ := hl
    exact ⟨x,hx,by rw [he]; decide +kernel⟩
  · apply natural_commutator_eq_of_image d
      ((oddFactor_le π D.L _).trans (actorPreimage_le π _))
      (I_normalizes_oddFactor d _)
    obtain ⟨x,hx,he⟩ := hr
    exact ⟨x,hx,by rw [he]; decide +kernel⟩

private theorem oddFactor_odd_index (K : Subgroup (S₃ × S₃)) :
    Odd ((D.S g).subgroupOf
      (oddFactor (moduleProjection d.quotientSymmetricEquiv) D.L K)).index := by
  let X := oddFactor (moduleProjection d.quotientSymmetricEquiv) D.L K
  have hXL : X ≤ D.L := by
    rintro x ⟨a, _, rfl⟩
    exact a.property.1
  let : ((D.S g).subgroupOf D.L).Normal := normal_subgroupOf_of_le_normalizer
    ((show D.L ≤ D.I g from d.I_eq_LU.symm ▸ le_sup_left).trans (core_normalized D g))
  have hd := ((D.S g).subgroupOf D.L).relIndex_dvd_index_of_normal (X.subgroupOf D.L)
  rw [relIndex_subgroupOf hXL] at hd
  exact (odd_source_index d d.I_eq_LU).of_dvd_nat hd

end CFSG.Quasithin.Chapter15.Section03.Nonabelian.Fusion.Source50.PairGeometry

open Subgroup InvertedCubicTensor
open scoped commutatorElement IsMulCommutative
open Representation.BinaryOffender Representation.BinaryQuadraticPair
open CFSG.Quasithin.ChapterG.Section02.OrthogonalPlusFour
open CFSG.Quasithin.ChapterG.Section02.OrthogonalPlusFour.Chapter15Collapse

namespace CFSG.Quasithin.Chapter15.Section03.Nonabelian.Fusion.Source50.PairGeometry
variable {G : Type*} [Group G] {I P V A B X : Subgroup G}
  {M : Type*} [AddCommGroup M] [Module (ZMod 2) M]
  {ρ : Representation (ZMod 2) I M}

private theorem commutator_le_of_image_fixed
    (c : Representation.BinaryConjugationSection I P V ρ)
    (hAP : A ≤ P) (hXI : X ≤ I)
    (hfix : ∀ x : I, (x : G) ∈ X → ∀ v ∈ c.imageSpace A, ρ x v = v) :
    ⁅A,X⁆ ≤ V := by
  rw [commutator_comm]
  apply commutator_le.mpr
  intro x hx a ha
  let p : P := ⟨a,hAP ha⟩
  let xi : I := ⟨x,hXI hx⟩
  let pa : P := ⟨x * a * x⁻¹,
    le_normalizer_iff.mp c.normalized x (hXI hx) a (hAP ha)⟩
  have he : c.coordinates pa = c.coordinates p := by
    apply Multiplicative.toAdd.injective
    exact (c.equivariant xi p).trans
      (hfix xi hx _ ((c.mem_imageSpace_iff A _).mpr ⟨p,ha,rfl⟩))
  have hq : c.coordinates (pa * p⁻¹) = 1 := by rw [map_mul,map_inv,he,mul_inv_cancel]
  have hm := (c.coordinates_eq_one_iff (pa * p⁻¹)).mp hq
  simpa only [pa, p, Subgroup.coe_mul, Subgroup.coe_inv, commutatorElement_def] using hm

private theorem upper_double_commutator_le
    {π : I →* S₃ × S₃} {σ : Representation (ZMod 2) (S₃ × S₃) M}
    (c : Representation.BinaryConjugationSection I P V (σ.comp π))
    {Y : Subgroup G} (r : ProductDecomposition σ)
    (hleft : c.imageSpace ⁅P, oddFactor π Y ProductDecomposition.leftFactor⁆ =
      r.left.toSubmodule)
    (hfixed : r.left.toSubmodule = fixedSpace (σ.comp π)
      ((actorPreimage π ProductDecomposition.rightFactor).subgroupOf I))
    (hAP : A ≤ P) :
    ⁅⁅A, oddFactor π Y ProductDecomposition.leftFactor⁆,
      oddFactor π Y ProductDecomposition.rightFactor⁆ ≤ V := by
  have hX₁I := (oddFactor_le π Y ProductDecomposition.leftFactor).trans
    (actorPreimage_le π ProductDecomposition.leftFactor)
  have hX₂I := (oddFactor_le π Y ProductDecomposition.rightFactor).trans
    (actorPreimage_le π ProductDecomposition.rightFactor)
  have hBP : ⁅A, oddFactor π Y ProductDecomposition.leftFactor⁆ ≤ P :=
    (commutator_mono hAP le_rfl).trans
      (le_normalizer_iff_commutator_le_left.mp (hX₁I.trans c.normalized))
  apply commutator_le_of_image_fixed c hBP hX₂I
  intro x hx v hv
  have hv' := c.imageSpace_mono (commutator_mono hAP le_rfl) hv
  rw [hleft,hfixed] at hv'
  exact hv' ⟨x, (oddFactor_le π Y ProductDecomposition.rightFactor) hx⟩

end CFSG.Quasithin.Chapter15.Section03.Nonabelian.Fusion.Source50.PairGeometry
namespace CFSG.Quasithin.Chapter15.Section03.Nonabelian.Fusion.Source50.PairGeometry
open Subgroup InvertedCubicTensor
open scoped IsMulCommutative
open Representation.BinaryOffender Representation.BinaryQuadraticPair
open CFSG.Quasithin.ChapterG.Section02.Setup
open CFSG.Quasithin.ChapterG.Section02.OrthogonalPlusFour
open CFSG.Quasithin.ChapterG.Section02.OrthogonalPlusFour.Chapter15Collapse
variable {G : Type*} [Group G] [Finite G]
  {D : CFSG.Quasithin.ChapterG.Section02.Setup G} {g : G}

/-- The upper natural types split canonically from the lower tensor type,
using the actual two residual actors and their permutation by T. -/
private theorem source_center_split_of_factorPermutation (d : Hypothesis D g)
    (hOmega : omegaCenter D.T ≤ D.VL)
    (hperm : ∀ t ∈ D.T,
      let X₁ := oddFactor (moduleProjection d.quotientSymmetricEquiv) D.L
        ProductDecomposition.leftFactor
      let X₂ := oddFactor (moduleProjection d.quotientSymmetricEquiv) D.L
        ProductDecomposition.rightFactor
      (X₁.map (MulAut.conj t).toMonoidHom = X₁ ∧
        X₂.map (MulAut.conj t).toMonoidHom = X₂) ∨
      (X₁.map (MulAut.conj t).toMonoidHom = X₂ ∧
        X₂.map (MulAut.conj t).toMonoidHom = X₁)) :
    ∃ C : Subgroup G, centerIn (D.S g) = D.VL ⊔ C ∧
      Disjoint C D.VL ∧ D.T ≤ normalizer (C : Set G) := by
  let A := centerIn (D.S g)
  let π := moduleProjection d.quotientSymmetricEquiv
  let X₁ := oddFactor π D.L ProductDecomposition.leftFactor
  let X₂ := oddFactor π D.L ProductDecomposition.rightFactor
  have hAP : A ≤ D.S g := inf_le_left
  have hcentral : A ≤ centralizer (D.S g : Set G) := inf_le_right
  let : IsMulCommutative A := le_centralizer_iff_isMulCommutative.mp
    (hcentral.trans (centralizer_le hAP))
  have hX₁I : X₁ ≤ D.I g := (oddFactor_le π D.L _).trans (actorPreimage_le π _)
  have hX₂I : X₂ ≤ D.I g := (oddFactor_le π D.L _).trans (actorPreimage_le π _)
  have hIX₁ : D.I g ≤ normalizer (X₁ : Set G) := I_normalizes_oddFactor d _
  have hIX₂ : D.I g ≤ normalizer (X₂ : Set G) := I_normalizes_oddFactor d _
  have hIA : D.I g ≤ normalizer (A : Set G) := normalizes_centerIn (core_normalized D g)
  have hVA : D.VL ≤ A := d.central_first_layer
  have hdouble : ⁅⁅A,X₁⁆,X₂⁆ = D.VL := by
    apply le_antisymm
    · let := moduleSectionNormal d d.I_eq_LU
      let := moduleSectionElementary d d.I_eq_LU d.S_normalizes_U d.S_eq_coreProduct
      obtain ⟨f⟩ := d.source_module_data
      have hm := source_oddFactor_modules π D.L (d.I_eq_LU.symm ▸ le_sup_left)
        d.quotientSymmetricEquiv_L_image f.representation f.conjugation f.decomposition
      have hb := upper_double_commutator_le f.conjugation f.decomposition hm.1 f.left_fixed hAP
      exact hb.trans (source_collapse d hOmega).2.2.2.2.2.le
    · obtain ⟨hl,hr⟩ := natural_oddFactor_commutators d
      have hmove : D.VL ≤ ⁅A,X₁⁆ := hl.symm.le.trans (commutator_mono hVA le_rfl)
      exact hr.symm.le.trans (commutator_mono hmove le_rfl)
  have hs := two_actor_split D.T (D.S g) A D.VL X₁ X₂ d.base.binary_T_isPGroup
    hAP d.S_le_T hcentral (hX₁I.trans hIA) (hX₂I.trans hIA)
    (hX₁I.trans hIX₂) (hX₂I.trans hIX₁)
    (oddFactor_odd_index d _) (oddFactor_odd_index d _) hdouble
  refine ⟨(A ⊓ centralizer (X₁ : Set G)) ⊔ (A ⊓ centralizer (X₂ : Set G)),
    hs.1, hs.2.symm, ?_⟩
  exact fixed_sum_normalized D.T A X₁ X₂ (normalizes_centerIn d.T_normalizes_core) hperm

end CFSG.Quasithin.Chapter15.Section03.Nonabelian.Fusion.Source50.PairGeometry

namespace CFSG.Quasithin.Chapter15.Section03.Nonabelian.Fusion.Source50.PairGeometry
open CFSG.Quasithin.Chapter15.Section03.Nonabelian.Fusion.Source50.PairGeometry
open CFSG.Quasithin.Chapter15.Section03
open CFSG.Quasithin.Chapter15.Section03.Nonabelian
variable {G : Type*} [Group G] [Finite G] {D : CFSG.Quasithin.ChapterG.Section02.Setup G} {g : G}

/-- The canonical split is constructed from the two source residual factors.
Their permutation by T is transported through the literal I/O₂(I) quotient. -/
theorem source_center_split (d : Hypothesis D g)
    (hOmega : omegaCenter D.T ≤ D.VL) :
    ∃ C : Subgroup G, centerIn (D.S g) = D.VL ⊔ C ∧
      Disjoint C D.VL ∧ D.T ≤ normalizer (C : Set G) :=
  source_center_split_of_factorPermutation d hOmega (residual_factors_permuted d)

/-- The exact center statements and extraspeciality in 15.3.55, deduced from
the proved G.2.6 action and the earlier omega-center condition. -/
theorem source_extraspecial (d : Hypothesis D g)
    (hOmega : omegaCenter D.T ≤ D.VL) :
    IsExtraspecial 2 D.U ∧ center D.U = D.V₁.subgroupOf D.U ∧
      D.VL = (center (D.S g)).map (D.S g).subtype :=
  source_extraspecial_of_split d hOmega (source_center_split d hOmega)

/-- Original 15.3.55 on the actual closure U and pair P. In particular the
last equality is the embedded center of P, never its ambient centralizer. -/
theorem literal_extraspecial
    {Z ZS Zperp V Y T : Subgroup G} {g : G}
    (hZS : ZS ≤ Zperp) (hperp : Zperp ≤ closureU Z ZS)
    (hspan : localSpan Z Y = V)
    (h26 : Hypothesis (Chapter15.setup Z Zperp Y T) g)
    (hOmega : omegaCenter T = Z) :
    IsExtraspecial 2 (closureU Z ZS) ∧
      center (closureU Z ZS) = Z.subgroupOf (closureU Z ZS) ∧
      V = (center (pairP Z ZS g)).map (pairP Z ZS g).subtype := by
  let D := Chapter15.setup Z Zperp Y T
  change Hypothesis D g at h26
  have hu : D.U = closureU Z ZS := Chapter15.closure_eq hZS hperp
  have hs : D.S g = pairP Z ZS g := Chapter15.S_eq g hZS hperp
  have hv : D.VL = V := Chapter15.VL_eq hspan
  have hp : D.V₁ = Z := rfl
  have hOmegaD : omegaCenter D.T ≤ D.VL := by
    change omegaCenter T ≤ D.VL
    rw [hOmega]
    exact point_le_VL D
  have hh := source_extraspecial h26 hOmegaD
  rw [hu, hs, hv, hp] at hh
  exact hh

end CFSG.Quasithin.Chapter15.Section03.Nonabelian.Fusion.Source50.PairGeometry
