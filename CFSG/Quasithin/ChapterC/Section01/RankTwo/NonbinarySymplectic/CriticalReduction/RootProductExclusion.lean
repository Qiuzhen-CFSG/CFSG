module
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.CriticalReduction.RootProductCommutator
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.CriticalReduction.RadiusGrowth
public import Theory.GroupTheory.NormalSectionTwoResidual

/-!
# Root-product exclusion at every original nonbinary degree

The actual rank-one residual moves U-alpha and therefore escapes Q-alpha.
Its commutator with the whole Q-alpha lies in U-alpha. The normal section
Q-alpha/U-alpha is thus centralized by an actor outside the simple vertex
quotient's kernel. Simplicity makes the whole vertex residual centralize
that same section. At distance at least four the radius lies in Q-alpha;
its displacement would therefore lie in Z-alpha, contrary to the original
common-edge normality obstruction and MS3.

This proves MS93 (5.1), printed pp.912--913, on the minimum characteristic
replacement, using the previously proved removal of the outer action.
The field degree and all central attachments are retained. Selection of
source paths and the terminal distance exclusions remain subsequent steps.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped Pointwise
open Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93
namespace CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic
open ChapterB.QuasisimpleSource MSCentralOrbit
variable {H F : Type*} [Group H] [Finite H] [Field F] [Finite F] [CharP F 2]
variable {K R : Subgroup H} {n : ℕ} (h : Input K R n F)
variable (d : CharacteristicReduction K R)
include h

theorem Input.replacement_root_product_excluded
    (geometry : Geometry d.radical) (hb : 4 ≤ geometry.b d.radical)
    {a t : Vertex d.radical} (ha : color d.radical a = false)
    (hat : Adjacent d.radical a t)
    (E₁ E₂ : Subgroup (FreeAmalgam d.radical))
    (hE₁ : E₁ ≤ Q d.radical t) (hE₂ : E₂ ≤ Q d.radical t)
    (hc₁ : (Q d.radical a).relIndex E₁ = Nat.card F)
    (hc₂ : (Q d.radical a).relIndex E₂ = Nat.card F)
    (hi₁ : (centralizer (E₁ : Set (FreeAmalgam d.radical))).relIndex
      (U d.radical a) = Nat.card F)
    (hi₂ : (centralizer (E₂ : Set (FreeAmalgam d.radical))).relIndex
      (U d.radical a) = Nat.card F)
    : ¬ (Subgroup.SmallMover.join (U d.radical a) (Q d.radical a)
        (Q d.radical t) (Nat.card F ^ 2) : Set (FreeAmalgam d.radical)) ⊆
      (E₁ : Set (FreeAmalgam d.radical)) * (E₂ : Set (FreeAmalgam d.radical)) := by
  intro hprod
  obtain ⟨E₀,hE₀,I,hI,hQI,C,hCI,hCn,hgen,heC,hfit,hres,hP,hmoves,hcomm,hcommZ⟩ :=
    h.replacement_root_product_core_commutator d geometry hb ha hat
      E₁ E₂ hE₁ hE₂ hc₁ hc₂ hi₁ hi₂ hprod
  obtain ⟨E,hE,f,hf,hfQ,hrest⟩ := h.replacement_inner_natural_action d geometry hb ha
  let S := stabilizer d.radical a
  let Q₀ := (Q d.radical a).subgroupOf S
  let U₀ := (U d.radical a).subgroupOf S
  let L := (pResidual 2 C).map C.subtype
  let T := L.subgroupOf S
  have hQa : Q d.radical a ≤ S := fun _ hx => hx.1
  have hUa : U d.radical a ≤ S := (U_le_Z a).trans (Z_le_stabilizer d.radical a)
  have hLa : L ≤ S := (map_subtype_le _).trans (hCI.trans hI)
  let : Q₀.Normal := (normal_subgroupOf_iff_le_normalizer hQa).mpr (Q_normalized d.radical a)
  let : U₀.Normal := (normal_subgroupOf_iff_le_normalizer hUa).mpr (U_normalized a)
  have hlarge : 3 < Nat.card E.Carrier := by
    rw [E.card_eq,hE]
    exact (by decide : 3 < 2^2).trans_le (Nat.pow_le_pow_right (by decide) h.nonbinary)
  let := Theory.SpecificGroups.SymplecticFour.SimpleQuotients.isSimpleGroup hlarge
  let : IsSimpleGroup (Matrix.symplecticGroup (Fin 2) E.Carrier) :=
    Theory.SpecificGroups.SymplecticFour.EvenProjective.equiv.isSimpleGroup
  have hk : IsPGroup 2 f.ker := by
    have hp := Q_isPGroup d.radical (h.replacement_two_group d) (h.replacement_core_le d) a ha
    exact (hfQ.symm ▸ hp).of_injective
      (f.ker.equivMapOfInjective S.subtype S.subtype_injective).toMonoidHom
      (f.ker.equivMapOfInjective S.subtype S.subtype_injective).injective
  have hT : ¬ T ≤ f.ker := by
    intro hTk
    have hm := map_mono (f := S.subtype) hTk
    rw [map_subgroupOf_eq_of_le hLa,hfQ] at hm
    apply hmoves
    apply bot_unique
    exact (commutator_mono (U_le_Z a) hm).trans_eq (Z_centralizes_Q d.radical a ha)
  have hc : ⁅Q₀,T⁆ ≤ U₀ := by
    apply (map_le_map_iff_of_injective S.subtype_injective).mp
    rw [map_commutator,map_subgroupOf_eq_of_le hQa,map_subgroupOf_eq_of_le hLa,
      map_subgroupOf_eq_of_le hUa]
    exact hcomm
  have hwhole := commutator_pResidual_le_of_simple_kernel_escape 2 f hf hk Q₀ U₀ T hT hc
  have hamb : ⁅Q d.radical a,Ltilde d.radical a⁆ ≤ U d.radical a := by
    have hh := map_mono (f := S.subtype) hwhole
    rwa [map_commutator,map_subgroupOf_eq_of_le hQa,map_subgroupOf_eq_of_le hUa] at hh
  have hne : Z d.radical a ≠ ⊥ := by
    obtain ⟨z,hz⟩ := criticalPair_exists d.radical a (geometry.exists_critical a ha)
    intro he
    exact hz.2 (he ▸ bot_le)
  apply Sp4Four.radius_moving_not_le_Z_of_residual_edge_generation
    (h.replacement_characteristic d) (h.replacement_residual_edge_generation d)
    geometry (by omega) ha hat hne
  exact ((commutator_mono (geometry.V_le_Q (by omega) a ha) le_rfl).trans hamb).trans (U_le_Z a)

end CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic
