module
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.DistanceTwo.Geometry.PlaneMovement.PointImage.Source

/-!
# A lower bound for whole-cover displacement

Two commuting involutions witnessing nonquadraticity give two independent
displacements modulo the fixed space: each fixes its own displacement and
moves the other. Thus the moved image modulo fixed vectors has order at least
four. The literal quotient conjugation action translates this into the native
edge index, without removing the central fixed line or choosing a complement.

The application uses the proved elementary radical image, retaining its earlier
LocalCalculations and radical-derived hypotheses. Full/Source consumes the
bound to discharge PlaneMovementInput. Source: MS93 (3.6), printed p.871.
-/

public noncomputable section
open Subgroup Representation Representation.BinaryOffender BinaryPermutation
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.DistanceTwo.Geometry.PlaneMovement

theorem nonquadratic_moved_quotient_four {K V : Type*} [Group K]
    [AddCommGroup V] [Module (ZMod 2) V] [Finite V]
    (ρ : Representation (ZMod 2) K V) (A : Subgroup K) [IsElementaryAbelian 2 A]
    (hn : ¬ IsQuadratic ρ A) :
    4 ≤ Nat.card ((subspaceCommutator ρ ⊤ A).map (fixedSpace ρ A).mkQ) := by
  classical
  obtain ⟨a,ha,b,hb,v,hn⟩ : ∃ a ∈ A, ∃ b ∈ A, ∃ v, ρ a (ρ b v-v) ≠ ρ b v-v := by
    simpa only [IsQuadratic,not_forall,exists_prop] using hn
  let δ (g : K) : V →ₗ[ZMod 2] V := ρ g - LinearMap.id
  let x := δ a v
  let y := δ b v
  have hxx : δ a x = 0 := by
    exact sub_eq_zero.mpr (involution_fixes_displacement ρ
      (by simpa only [pow_two] using elemPow_eq_one_of_isElementaryAbelian (p := 2) a ha) v)
  have hyy : δ b y = 0 := by
    exact sub_eq_zero.mpr (involution_fixes_displacement ρ
      (by simpa only [pow_two] using elemPow_eq_one_of_isElementaryAbelian (p := 2) b hb) v)
  have hy : δ a y ≠ 0 := sub_ne_zero.mpr hn
  have hxy : δ b x = δ a y := by
    have hab : a*b=b*a := congrArg Subtype.val (mul_comm (⟨a,ha⟩ : A) ⟨b,hb⟩)
    dsimp only [δ,x,y,LinearMap.sub_apply,LinearMap.id_apply]
    simp only [map_sub,←Module.End.mul_apply,←map_mul,hab]
    abel
  have hx : δ b x ≠ 0 := hxy ▸ hy
  let D := subspaceCommutator ρ ⊤ A
  let C := fixedSpace ρ A
  have hxD : x ∈ D := Submodule.subset_span ⟨a,ha,v,Submodule.mem_top,rfl⟩
  have hyD : y ∈ D := Submodule.subset_span ⟨b,hb,v,Submodule.mem_top,rfl⟩
  let f : (ZMod 2 × ZMod 2) →ₗ[ZMod 2] V :=
    (LinearMap.fst (ZMod 2) (ZMod 2) (ZMod 2)).smulRight x +
      (LinearMap.snd (ZMod 2) (ZMod 2) (ZMod 2)).smulRight y
  have hfC : ∀ s, f s ∈ C → s = 0 := by
    intro s hs
    have hs0 (g : K) (hg : g ∈ A) : δ g (f s) = 0 :=
      sub_eq_zero.mpr (hs ⟨g,hg⟩)
    have h2 := hs0 a ha
    change δ a (s.1 • x + s.2 • y) = 0 at h2
    rw [map_add,map_smul,map_smul,hxx,smul_zero,zero_add] at h2
    have hs2 : s.2 = 0 := (smul_eq_zero.mp h2).resolve_right hy
    have h1 := hs0 b hb
    change δ b (s.1 • x + s.2 • y) = 0 at h1
    rw [map_add,map_smul,map_smul,hyy,smul_zero,add_zero] at h1
    have hs1 : s.1 = 0 := (smul_eq_zero.mp h1).resolve_right hx
    exact Prod.ext hs1 hs2
  let F := C.mkQ.comp f
  have hF : Function.Injective F := by
    apply (LinearMap.ker_eq_bot).mp
    apply le_antisymm _ bot_le
    intro s hs
    exact hfC s ((Submodule.Quotient.mk_eq_zero C).mp hs)
  let : Finite (V ⧸ C) := Finite.of_surjective C.mkQ C.mkQ_surjective
  let f' : (ZMod 2 × ZMod 2) → D.map C.mkQ := fun s =>
    ⟨F s,⟨f s,D.add_mem (D.smul_mem _ hxD) (D.smul_mem _ hyD),rfl⟩⟩
  have hinj : Function.Injective f' := fun a b he => hF (congrArg Subtype.val he)
  have hc := Nat.card_le_card_of_injective f' hinj
  simpa only [Nat.card_prod,Nat.card_zmod] using hc

open CFSG.Quasithin.ChapterC.BinaryMS.MS93 Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.NaturalSixControl.SymplecticDistanceTwo
open LargeDistance PairEstimates
universe u
variable {G : Type u} [Group G] [Finite G] {L R : Subgroup G}
  (h : SmallMSPair KnownSimple.IsKnownSimple L R) (e : CentralMarking L)
  (hz : center (L ⧸ pCore 2 L) = ⊥) (hn : InitialNatural h e hz)
  (d : Replacement L R)

include h e hz hn in
theorem native_displacement_index_ge_four
    (hl : LocalCalculations d.radical (replacementGeometry h d))
    (hb : replacementDistance h d = 2)
    (hlarge : ¬ core d.radical (alpha d.radical) ≤
      (frattini (Q d.radical (alpha d.radical))).map
        (Q d.radical (alpha d.radical)).subtype ⊔ X d.radical (alpha d.radical))
    (hder : ⁅d.radical,d.radical⁆ ≤ pCore 2 d.overgroup) :
    4 ≤ (omegaCenter d.radical).relIndex
      (⁅d.radical,replacementMoved d⁆ ⊔ omegaCenter d.radical) := by
  let := replacementMoved_normal h d
  let := moved_elementary h d
  let W := replacementMoved d
  let q := Recognition.sourceProjection h e hz hn d
  obtain ⟨o⟩ := exists_orderedOrbit (replacementGeometry h d)
    (replacement_radical_isPGroup h d) (replacement_core_le_radical h d) hl hb
  let a := earlyPair (replacement_radical_isPGroup h d)
    (replacement_core_le_radical h d) hl hb hlarge o
  let := a.quotient_elementary
  have hq := (sourceImageModel h e hz hn d a).onto
    (replacement_radical_isPGroup h d) (replacement_core_le_radical h d)
  let hk := (Recognition.sourceProjection_kernel h e hz hn d).trans
    (moved_centralizer h e hz hn d).symm
  let ρ := NormalElementaryQuotient.representation W q hq hk
  let A := d.radical.map q
  let C := fixedSpace ρ A
  let D := ⁅W,d.radical⁆
  let p : W →* Multiplicative ((Additive W) ⧸ C) :=
    C.mkQ.toAddMonoidHom.toMultiplicativeRight
  let := (radical_image_elementary_eight h e hz hn d hl hb hlarge hder).1
  have hfour := nonquadratic_moved_quotient_four ρ A
    (moved_action_nonquadratic h e hz hn d hq hb hlarge)
  have hWI : W ≤ d.radical := (replacementMoved_le_omegaCenter h d).trans
    ((omegaCenter_le _).trans (replacement_core_le_radical h d))
  have hp : p.ker = (omegaCenter d.radical).subgroupOf W := by
    ext w
    change C.mkQ (Additive.ofMul w) = 0 ↔ (w:d.overgroup) ∈ omegaCenter d.radical
    rw [←LinearMap.mem_ker,Submodule.ker_mkQ,
      NormalElementaryQuotient.mem_fixedSpace_image W q hq hk]
    rw [mem_omegaCenter_iff]
    exact ⟨fun hw => ⟨hWI w.property,
      elemPow_eq_one_of_isElementaryAbelian (p := 2) _ w.property,hw⟩,fun hw => hw.2.2⟩
  have hc : Nat.card ((subspaceCommutator ρ ⊤ A).map C.mkQ) =
      Nat.card ((D.subgroupOf W).map p) := by
    rw [←NormalElementaryQuotient.commutatorSpace_eq W q hq hk]
    rfl
  rw [hc,←Subgroup.relIndex_ker,hp,relIndex_subgroupOf (commutator_le_left W d.radical)] at hfour
  rw [commutator_comm W d.radical] at hfour
  exact hfour.trans (relIndex_le_of_le_right le_sup_left (index_ne_zero_of_finite (H :=
    (omegaCenter d.radical).subgroupOf (⁅d.radical,replacementMoved d⁆ ⊔ omegaCenter d.radical))))

end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.DistanceTwo.Geometry.PlaneMovement
