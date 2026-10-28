module

public import CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ModelExclusions.PointTransport
public import Theory.SpecificGroups.PSL3Two.Parabolics.Subgroups.Coordinates
public import Theory.Representation.PSL3Two.SmallModules
public import Theory.GroupTheory.PCoreLocalSetup
public import Theory.Representation.BinaryOffender.FaithfulRankOne

/-!
# Binary three-dimensional point cores

The intrinsic two-core of a nonzero-vector stabilizer in SL₃(2) lies in
its four-group of point shears. That group fixes just the point line;
faithfulness handles its proper subgroups. Equivariant conjugation then
proves the absence of strong offenders at every nonzero vector.

The Sylow-intersection argument follows the coordinate line-core calculation
in `Theory.SpecificGroups.PSL3Two.Parabolics.LineCore`. The application is
Aschbacher–Smith, combined manuscript, printed p.1145, the L₃(2) paragraph
of 15.3.49, with the natural-module alternative of B.5.1.
-/

@[expose] public section

open Matrix Subgroup Representation Representation.BinaryOffender
open CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ModelExclusions
open Matrix.PSL3Two
open CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination
namespace CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ModelExclusions.PointCases.Binary
abbrev Vector := Fin 3 → ZMod 2
abbrev natural := BinaryLinearThree.W

def shear : Multiplicative (ZMod 2 × ZMod 2) →* SL where
  toFun c := ⟨!![1,c.toAdd.1,c.toAdd.2; 0,1,0; 0,0,1], by simp [det_fin_three]⟩
  map_one' := by apply Subtype.ext; decide
  map_mul' c d := by
    apply Subtype.ext
    change !![1,c.toAdd.1+d.toAdd.1,c.toAdd.2+d.toAdd.2; 0,1,0; 0,0,1] =
      !![1,c.toAdd.1,c.toAdd.2; 0,1,0; 0,0,1] *
        !![1,d.toAdd.1,d.toAdd.2; 0,1,0; 0,0,1]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_three, add_comm]
def R : Subgroup SL := shear.range

theorem shear_injective : Function.Injective shear := by
  intro c d h
  exact Prod.ext (congrArg (fun g : SL => g.val 0 1) h)
    (congrArg (fun g : SL => g.val 0 2) h)

theorem card_R : Nat.card R = 4 := by
  change Nat.card shear.range = 4
  rw [← Nat.card_congr (MonoidHom.ofInjective shear_injective).toEquiv, Nat.card_eq_fintype_card]
  decide

private theorem core_le_borel : localTwoCore pointParabolicSL ≤ borelSL := by
  have hcard : Nat.card (borelSL.subgroupOf pointParabolicSL) = 8 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe
      (show borelSL ≤ pointParabolicSL from inf_le_left)).toEquiv]
    exact card_borelSL
  let sylow : Sylow 2 pointParabolicSL := Sylow.ofCard
    (borelSL.subgroupOf pointParabolicSL) (by
      rw [hcard, card_pointParabolicSL]
      decide +kernel)
  have hle := Subgroup.pCoreIn_le_sylow pointParabolicSL sylow
  simpa only [Subgroup.pCoreIn, localTwoCore, sylow, Sylow.coe_ofCard,
    Subgroup.map_subgroupOf_eq_of_le (show borelSL ≤ pointParabolicSL from inf_le_left)]
    using hle

theorem core_le_R : localTwoCore pointParabolicSL ≤ R := by
  rintro g ⟨x, hx, rfl⟩
  have hb := core_le_borel (Subgroup.mem_map_of_mem pointParabolicSL.subtype hx)
  obtain ⟨h10, h20, h21⟩ := (mem_borelSL_iff _).mp hb
  change x.val.val 1 0 = 0 at h10
  change x.val.val 2 0 = 0 at h20
  change x.val.val 2 1 = 0 at h21
  let s : pointParabolicSL :=
    ⟨⟨!![1,0,0; 0,0,1; 0,1,0], by decide⟩,
      (mem_pointParabolicSL_iff _).mpr ⟨rfl, rfl⟩⟩
  have hsinv : s⁻¹ = s := by
    apply inv_eq_of_mul_eq_one_right
    apply Subtype.ext
    apply Subtype.ext
    decide
  have hc : s * x * s⁻¹ ∈ pCore 2 pointParabolicSL :=
    Subgroup.Normal.conj_mem inferInstance x hx s
  have hb' := core_le_borel (Subgroup.mem_map_of_mem pointParabolicSL.subtype hc)
  have h12 := ((mem_borelSL_iff _).mp hb').2.2
  rw [hsinv] at h12
  change ((!![1,0,0; 0,0,1; 0,1,0] * x.val.val *
    !![1,0,0; 0,0,1; 0,1,0]) : Matrix (Fin 3) (Fin 3) (ZMod 2)) 2 1 = 0 at h12
  simp [Matrix.mul_apply, vecMul, dotProduct, Fin.sum_univ_three] at h12
  have hd := x.val.property
  rw [det_fin_three] at hd
  simp only [h10, h20, h21, h12, mul_zero, zero_mul, sub_zero, add_zero] at hd
  have hdiag : ∀ a b c : ZMod 2, a * b * c = 1 → a = 1 ∧ b = 1 ∧ c = 1 := by decide
  obtain ⟨h00, h11, h22⟩ := hdiag _ _ _ hd
  refine ⟨Multiplicative.ofAdd (x.val.val 0 1, x.val.val 0 2), ?_⟩
  apply Subtype.ext
  change !![1,x.val.val 0 1,x.val.val 0 2; 0,1,0; 0,0,1] = x.val.val
  ext i j
  fin_cases i <;> fin_cases j <;> simp [h00, h11, h22, h10, h20, h21, h12]

private noncomputable def fixedCoordinate : fixedSpace natural R →ₗ[ZMod 2] ZMod 2 :=
  (LinearMap.proj 0).comp (fixedSpace natural R).subtype

private theorem fixedCoordinate_injective : Function.Injective fixedCoordinate := by
  apply LinearMap.ker_eq_bot.mp
  apply le_bot_iff.mp
  intro v hv
  have h0 : v.val 0 = 0 := hv
  have h1 := congrFun (v.property ⟨shear (Multiplicative.ofAdd (1,0)), ⟨_, rfl⟩⟩) 0
  have h2 := congrFun (v.property ⟨shear (Multiplicative.ofAdd (0,1)), ⟨_, rfl⟩⟩) 0
  change (!![1,1,0;0,1,0;0,0,1].mulVec v.val) 0 = v.val 0 at h1
  change (!![1,0,1;0,1,0;0,0,1].mulVec v.val) 0 = v.val 0 at h2
  simp [mulVec, dotProduct, Fin.sum_univ_three, h0] at h1 h2
  apply Subtype.ext
  funext i
  fin_cases i <;> assumption

theorem codim_R : 2 ≤ fixedCodim natural R := by
  have hf := LinearMap.finrank_le_finrank_of_injective fixedCoordinate_injective
  have hc := fixedCodim_add_finrank natural R
  have hd : Module.finrank (ZMod 2) Vector = 3 := by simp [Vector]
  rw [Module.finrank_self] at hf
  change fixedCodim natural R + _ = Module.finrank (ZMod 2) Vector at hc
  omega

private theorem faithful : Function.Injective natural := by
  intro g h he
  apply SpecialLinearGroup.toLin'_injective
  exact LinearEquiv.toLinearMap_injective he

theorem not_strong_of_le_R {A : Subgroup SL} (hA : A ≤ R) : ¬ IsStrongOffender natural A := by
  intro hs
  have hc : Nat.card A ≤ 4 := (Subgroup.card_le_of_le hA).trans_eq card_R
  have hp := fixedCodim_pos_of_faithful natural faithful hs.1.1
  by_cases he : A = R
  · subst A
    have hr : rank R = 2 := by rw [BinaryOffender.rank, card_R]; decide
    have h := codim_R
    have hlt := hs.2
    rw [hr] at hlt
    omega
  · have hn : Nat.card A < 4 := lt_of_le_of_ne hc (fun h =>
      he (Subgroup.eq_of_le_of_card_ge hA (by rw [card_R, h])))
    have hr : rank A < 2 := Nat.log_lt_of_lt_pow' (by decide : 2 ≠ 0) hn
    have := hs.2
    omega

theorem point_stabilizer : pointStabilizer natural (![1,0,0] : Vector) = pointParabolicSL := by
  ext g
  rw [mem_pointParabolicSL_iff]
  change g.val.mulVec ![1,0,0] = ![1,0,0] ↔ _
  constructor
  · intro h
    constructor
    · simpa [mulVec, dotProduct, Fin.sum_univ_three] using congrFun h 1
    · simpa [mulVec, dotProduct, Fin.sum_univ_three] using congrFun h 2
  · rintro ⟨h10,h20⟩
    have hd := g.property
    rw [det_fin_three] at hd
    have h00 : g.val 0 0 = 1 := by
      have hz : g.val 0 0 ≠ 0 := by intro hz; simp [h10,h20,hz] at hd
      exact (by decide : ∀ a : ZMod 2, a ≠ 0 → a = 1) _ hz
    ext i
    fin_cases i <;> simp [mulVec, dotProduct, Fin.sum_univ_three,h00,h10,h20]

theorem not_strong_standard {A : Subgroup SL}
    (hA : A ≤ localTwoCore (pointStabilizer natural (![1,0,0] : Vector))) : ¬ IsStrongOffender natural A := by
  rw [point_stabilizer] at hA
  exact not_strong_of_le_R (hA.trans core_le_R)

set_option maxRecDepth 10000 in
private theorem completion : ∀ v : Vector, v ≠ 0 → ∃ w u : Vector,
    (Matrix.of ![v,w,u]).transpose.det = 1 := by decide +kernel

theorem point_reachable (v : Vector) (hv : v ≠ 0) :
    ∃ g : SL, natural g (![1,0,0] : Vector) = v := by
  obtain ⟨w,u,h⟩ := completion v hv
  refine ⟨⟨(Matrix.of ![v,w,u]).transpose,h⟩, ?_⟩
  change (Matrix.of ![v,w,u]).transpose.mulVec ![1,0,0] = v
  ext i
  simp [mulVec, dotProduct, Fin.sum_univ_three]

private theorem action_conj (g a : SL) (v : Vector) :
    natural g (natural a v) = natural ((MulAut.conj g) a) (natural g v) := by
  simp only [← Module.End.mul_apply, ← map_mul, MulAut.conj_apply]
  rw [show g * a * g⁻¹ * g = g * a by group]

theorem not_strong_point (v : Vector) (hv : v ≠ 0) {A : Subgroup SL}
    (hA : A ≤ localTwoCore (pointStabilizer natural v)) : ¬ IsStrongOffender natural A := by
  intro hs
  obtain ⟨g,hg⟩ := point_reachable v hv
  let E : Vector ≃ₗ[ZMod 2] Vector := LinearEquiv.ofBijective (natural g⁻¹) (natural.apply_bijective g⁻¹)
  have hE : ∀ a v, E (natural a v) = natural ((MulAut.conj g⁻¹) a) (E v) := action_conj g⁻¹
  have hz : E v = (![1,0,0] : Vector) := by
    change natural g⁻¹ v = _
    rw [← hg, ← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one]
    rfl
  apply exclude_strong_at_identified_point natural natural (MulAut.conj g⁻¹) E hE v
    (pointStabilizer natural v) A rfl hA _ hs
  rw [hz]
  exact fun _ hB => not_strong_standard hB

theorem point_stabilizer_ne_top (v : Vector) (hv : v ≠ 0) :
    pointStabilizer natural v ≠ ⊤ := by
  intro ht
  obtain ⟨g,hg⟩ := point_reachable v hv
  let E : Vector ≃ₗ[ZMod 2] Vector := LinearEquiv.ofBijective (natural g) (natural.apply_bijective g)
  have he := pointStabilizer_map_equivariant natural natural (MulAut.conj g) E (action_conj g)
    (![1,0,0] : Vector)
  change (pointStabilizer natural (![1,0,0] : Vector)).map (MulAut.conj g).toMonoidHom =
    pointStabilizer natural (natural g (![1,0,0] : Vector)) at he
  rw [hg, ht, point_stabilizer] at he
  have htop : pointParabolicSL = ⊤ := Subgroup.map_injective
    (MulAut.conj g).injective (he.trans (Subgroup.map_top_of_surjective _
      (MulAut.conj g).surjective).symm)
  have hn : pointParabolicSL ≠ ⊤ := by
    intro h
    have hm : (⟨!![0,1,0;1,0,0;0,0,1], by decide⟩ : SL) ∈ pointParabolicSL :=
      by rw [h]; trivial
    have := (mem_pointParabolicSL_iff _).mp hm
    exact (by decide : (1 : ZMod 2) ≠ 0) this.1
  exact hn htop
end CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ModelExclusions.PointCases.Binary
