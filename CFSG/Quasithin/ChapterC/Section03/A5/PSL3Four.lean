module
public import CFSG.Quasithin.ChapterC.Section03.A5.ModelSeparation
public import CFSG.Quasithin.ChapterC.Section01.BlockTypes.SL2Affine
public import CFSG.Quasithin.ChapterC.Section01.RankOne.Solvable.Source.Transport
public import Theory.SpecificGroups.PSL3Four.CentralCover.FullPlaneNormalizer
public import Theory.GroupTheory.CharacteristicCentralizerFusion

/-!
# The deleted-five block does not embed in PSL₃(4)

An alternating-five block with elementary commutator layer of order sixteen
has order at least 16 · 60. In PSL₃(4), the full normalizer of that layer is
an affine parabolic of exactly this order. Thus the block equals its full
normalizer and carries the natural SL₂(4) action, contradicting the cubic
fixed-vector distinction between the natural and deleted-five modules.

Source: Aschbacher–Smith 13.5.15, printed p.921, using the original A₅ block
and its elementary layer; the same model exclusion applies to C.3.1.
-/

public section
open Subgroup
namespace CFSG.Quasithin.ChapterC
open Matrix.PSL3Four Matrix.PSL3Four.ElementaryParabolic
open Matrix.PSL3Four.FullPlaneNormalizer
variable {G : Type*} [Group G] [Finite G]

/-- The literal block subgroup cannot occur in any group isomorphic to PSL₃(4). -/
theorem no_alternatingFive_of_psl3Four_equiv
    (e : G ≃* PSL) (A : Subgroup G) (hA : IsAlternatingBlock A 5)
    (hc : Nat.card ((blockU A).map A.subtype) = 16) : False := by
  let U := (blockU A).map A.subtype
  let := hA.2.1.elementary
  let : IsElementaryAbelian 2 U := IsElementaryAbelian.map A.subtype
  have hk : e.toMonoidHom.ker = ⊥ := (MonoidHom.ker_eq_bot_iff _).mpr e.injective
  obtain ⟨g,b,hN⟩ := full_plane_normalizer_alignment e.toMonoidHom e.surjective U
    (by rw [hk]; exact bot_le) (by rw [hk,card_bot,one_mul]; exact hc)
  let f := (MulAut.conj g).toMonoidHom.comp e.toMonoidHom
  have hf : Function.Surjective f := (MulAut.conj g).surjective.comp e.surjective
  have hfi : Function.Injective f := (MulAut.conj g).injective.comp e.injective
  have hfk : f.ker = ⊥ := (MonoidHom.ker_eq_bot_iff _).mpr hfi
  have hAN : A ≤ normalizer (U : Set G) :=
    A.le_normalizer.trans (normalizer_le_normalizer_characteristic_image A (blockU A))
  have hNcard : Nat.card (normalizer (U : Set G)) = 960 := by
    rw [hN,parabolic_card f hf b,hfk,card_bot,mul_one]
  have hUcard : Nat.card (blockU A) = 16 := by
    rw [←hc,card_map_of_injective A.subtype_injective]
  obtain ⟨a⟩ := hA.2.2.quotient_iso
  have hquot : Nat.card (A ⧸ pCore 2 A) = 60 := by
    rw [Nat.card_congr a.toEquiv,nat_card_alternatingGroup]
    norm_num
  have hcore : 16 ≤ Nat.card (pCore 2 A) := by
    rw [←hUcard]
    exact Nat.card_le_card_of_injective (inclusion blockU_le_core)
      (inclusion_injective blockU_le_core)
  have hlarge : 960 ≤ Nat.card A := by
    rw [card_eq_card_quotient_mul_card_subgroup (pCore 2 A),hquot]
    omega
  have hEq : A = normalizer (U : Set G) :=
    eq_of_le_of_card_ge hAN (by rw [hNcard]; exact hlarge)
  have hinj : Function.Injective (parabolicAffine f b) := by
    apply (MonoidHom.ker_eq_bot_iff _).mp
    rw [parabolicAffine_ker,hfk]
    change (liftedParabolic f b).subtype.ker = ⊥
    exact (MonoidHom.ker_eq_bot_iff _).mpr (liftedParabolic f b).subtype_injective
  let p := MulEquiv.ofBijective (parabolicAffine f b)
    ⟨hinj,parabolicAffine_surjective f hf b⟩
  let d := (MulEquiv.subgroupCongr (hEq.trans hN)).trans p
  exact hA.not_linearTwo_model
    ⟨Matrix.SL2.naturalAction F,⟨SL2Affine.blockModuleModel d⟩,fun _ _ => rfl⟩

end CFSG.Quasithin.ChapterC
