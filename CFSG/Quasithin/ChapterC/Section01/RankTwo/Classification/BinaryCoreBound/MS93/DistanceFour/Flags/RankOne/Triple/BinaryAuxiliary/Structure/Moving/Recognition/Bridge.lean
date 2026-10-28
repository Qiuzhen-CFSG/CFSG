module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Flags.RankOne.Triple.BinaryAuxiliary.Structure.Moving.Action
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Flags.RankOne.Triple.BinaryAuxiliary.Structure.Moving.Recognition.Space

/-!
# From source displacement estimates to the actual moving factor

Images of the literal ambient commutators are precisely the action-difference
spans in Y/U. The escaping two-group supplies a nonidentity reflection whose
displacement has order at most two, and the source two-residual still moves the
descended S3 representation. Given coordinates on its full moving subspace,
we lift them onto ([Y,P] sup U)/U, retaining the exact kernel U, the actor kernel
Q inside P, and the literal ambient conjugation equation.

All normality and residual transport are relative to the full actor. The
linear size bound and the final recognition are proved in separate modules.

Source: Meierfrankenfeld--Stellmacher (1993), (4.6.8), printed p.907.
-/

@[expose] public section
open Subgroup Stellmacher.PushingUp.AmalgamGraph
open Representation.BinaryOffender
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceFour.Flags.RankOne.BinaryAuxiliary.Moving
open Incident.Pairing.Transport.Natural.Kernel
universe u
variable {M : Type u} [Group M] {L R : Subgroup M}

namespace AuxiliaryModule
variable {source : LocalSource L R} {i : Bool} {d : M}

lemma mem_image_iff (b : AuxiliaryModule source i d) (A : Subgroup (FreeAmalgam R))
    (v : b.Space) : v ∈ b.image A ↔
      ∃ x : Y source i d, (x : FreeAmalgam R) ∈ A ∧ (b.projection x).toAdd = v := Iff.rfl

lemma commutator_image (b : AuxiliaryModule source i d)
    (E : Subgroup (FreeAmalgam R)) (hE : E ≤ localFlagActor source (!i) d) :
    b.image ⁅Y source i d, E⁆ =
      subspaceCommutator b.representation ⊤ (E.subgroupOf (localFlagActor source (!i) d)) := by
  let P := localFlagActor source (!i) d
  let T := subspaceCommutator b.representation ⊤ (E.subgroupOf P)
  let conj (g : P) (x : Y source i d) : Y source i d :=
    ⟨(g : FreeAmalgam R) * x * (g : FreeAmalgam R)⁻¹,
      (mem_normalizer_iff.mp (Y_normalized source i d g.property) x).mp x.property⟩
  have he (g : P) (x : Y source i d) :
      (b.projection (conj g x * x⁻¹)).toAdd =
        b.representation g (b.projection x).toAdd - (b.projection x).toAdd := by
    simp only [map_mul, map_inv, toAdd_mul, toAdd_inv,
      ← sub_eq_add_neg]
    rw [b.action g x (conj g x) rfl]
  apply le_antisymm
  · let J : Subgroup (Y source i d) := T.toAddSubgroup.toSubgroup.comap b.projection
    have hcomm : ⁅Y source i d, E⁆ ≤ J.map (Y source i d).subtype := by
      rw [commutator_comm]
      apply commutator_le.mpr
      intro g hg x hx
      let a : P := ⟨g, hE hg⟩
      let v : Y source i d := ⟨x, hx⟩
      refine ⟨conj a v * v⁻¹, ?_, rfl⟩
      change (b.projection (conj a v * v⁻¹)).toAdd ∈ T
      rw [he]
      exact Submodule.subset_span ⟨a, hg, (b.projection v).toAdd, Submodule.mem_top, rfl⟩
    intro v hv
    obtain ⟨x, hx, rfl⟩ := (b.mem_image_iff _ _).mp hv
    obtain ⟨y, hy, hyx⟩ := hcomm hx
    have hxy : y = x := Subtype.ext hyx
    exact hxy ▸ hy
  · apply Submodule.span_le.mpr
    rintro v ⟨g, hg, w, _, rfl⟩
    obtain ⟨x, hx⟩ := b.onto (Multiplicative.ofAdd w)
    have hx' : (b.projection x).toAdd = w := congrArg Multiplicative.toAdd hx
    apply (b.mem_image_iff _ _).mpr
    refine ⟨conj g x * x⁻¹, ?_, ?_⟩
    · rw [commutator_comm]
      exact commutator_mem_commutator hg x.property
    · rw [he, hx']

lemma image_sup_denominator (b : AuxiliaryModule source i d)
    (A : Subgroup (FreeAmalgam R)) (hA : A ≤ Y source i d) :
    b.image (A ⊔ secondFlagLayer source i d) = b.image A := by
  have hU : secondFlagLayer source i d ≤ Y source i d := second_le_Y source i d
  have hs : (A ⊔ secondFlagLayer source i d).subgroupOf (Y source i d) =
      A.subgroupOf (Y source i d) ⊔ (secondFlagLayer source i d).subgroupOf (Y source i d) :=
    subgroupOf_sup hA hU
  unfold image
  rw [hs, Subgroup.map_sup, ← b.kernel, Subgroup.map_ker_self]
  simp

end AuxiliaryModule

variable {source : LocalSource L R} {i : Bool} {d : M}

lemma AuxiliaryModule.descended_commutator_image (b : AuxiliaryModule source i d)
    (π : localFlagActor source (!i) d →* BinaryS3.Actor)
    (ρ : Representation (ZMod 2) BinaryS3.Actor b.Space)
    (ha : ∀ g v, b.representation g v = ρ (π g) v)
    (E : Subgroup (FreeAmalgam R)) (hE : E ≤ localFlagActor source (!i) d) :
    b.image ⁅Y source i d, E⁆ = subspaceCommutator ρ ⊤
      ((E.subgroupOf (localFlagActor source (!i) d)).map π) := by
  rw [b.commutator_image E hE]
  apply le_antisymm <;> apply Submodule.span_le.mpr
  · rintro _ ⟨g, hg, v, hv, rfl⟩
    rw [ha]
    exact Submodule.subset_span ⟨π g, mem_map_of_mem π hg, v, hv, rfl⟩
  · rintro _ ⟨_, ⟨g, hg, rfl⟩, v, hv, rfl⟩
    rw [← ha]
    exact Submodule.subset_span ⟨g, hg, v, hv, rfl⟩

lemma AuxiliaryModule.descended_moving_image (b : AuxiliaryModule source i d)
    (π : localFlagActor source (!i) d →* BinaryS3.Actor) (hπ : Function.Surjective π)
    (ρ : Representation (ZMod 2) BinaryS3.Actor b.Space)
    (ha : ∀ g v, b.representation g v = ρ (π g) v) :
    b.image (⁅Y source i d, localFlagActor source (!i) d⁆ ⊔ secondFlagLayer source i d) =
      (movedSpace ρ).toSubmodule := by
  rw [b.image_sup_denominator _ (le_normalizer_iff_commutator_le_left.mp (Y_normalized source i d)),
    b.descended_commutator_image π ρ ha _ le_rfl, subgroupOf_self,
    ← MonoidHom.range_eq_map, MonoidHom.range_eq_top.mpr hπ]
  rfl

lemma localFlagResidual_eq [Finite M] (source : LocalSource L R) (j : Bool) (d : M) :
    localFlagResidual source j d =
      (pResidual 2 (localFlagActor source j d)).map (localFlagActor source j d).subtype := by
  let e : flagParabolic source j ≃* localFlagActor source j d :=
    (MulAut.conj (embedM R d)).subgroupMap (flagParabolic source j)
  ext g
  change g ∈ (flagResidual source j).map (MulAut.conj (embedM R d)).toMonoidHom ↔ _
  constructor
  · rintro ⟨x, hx, hxg⟩
    rw [flagResidual_eq] at hx
    obtain ⟨y, hy, rfl⟩ := hx
    refine ⟨e y, map_pResidual_le 2 e.toMonoidHom (mem_map_of_mem _ hy), ?_⟩
    exact hxg
  · rintro ⟨x, hx, rfl⟩
    refine ⟨e.symm x, ?_, ?_⟩
    · rw [flagResidual_eq]
      exact mem_map_of_mem _
        (map_pResidual_le 2 e.symm.toMonoidHom (mem_map_of_mem _ hx))
    · exact congrArg Subtype.val (e.apply_symm_apply x)

lemma AuxiliaryModule.descended_residual_moves [Finite M] (b : AuxiliaryModule source i d)
    (π : localFlagActor source (!i) d →* BinaryS3.Actor)
    (ρ : Representation (ZMod 2) BinaryS3.Actor b.Space)
    (ha : ∀ g v, b.representation g v = ρ (π g) v)
    (hm : ¬ ⁅Y source i d, localFlagResidual source (!i) d⁆ ≤ secondFlagLayer source i d) :
    ¬ pResidual 2 BinaryS3.Actor ≤ ρ.ker := by
  intro hk
  apply hm
  apply (b.kernel_iff _ (map_mono (flagResidual_le source (!i)))).mp
  intro g hg
  change (g : FreeAmalgam R) ∈ localFlagResidual source (!i) d at hg
  rw [localFlagResidual_eq source (!i) d] at hg
  obtain ⟨a, ha', hag⟩ := hg
  have heq : a = g := Subtype.ext hag
  have hg' : g ∈ pResidual 2 (localFlagActor source (!i) d) := heq ▸ ha'
  have hπg : π g ∈ pResidual 2 BinaryS3.Actor :=
    map_pResidual_le 2 π (mem_map_of_mem π hg')
  change b.representation g = 1
  ext v
  rw [ha, show ρ (π g) = 1 from hk hπg]

private theorem two_subgroup_reflection (H : Subgroup BinaryS3.Actor) (hp : IsPGroup 2 H)
    (hne : H ≠ ⊥) : ∃ t : BinaryS3.Actor, t ^ 2 = 1 ∧ t ≠ 1 ∧ t ∈ H := by
  have orders : ∀ x : BinaryS3.Actor, x ^ 2 = 1 ∨ x ^ 3 = 1 := by decide +kernel
  obtain ⟨t, ht, htn⟩ := (bot_or_exists_ne_one H).resolve_left hne
  refine ⟨t, ?_, htn, ht⟩
  rcases orders t with h | h
  · exact h
  · have hc := hp.orderOf_coprime (by decide : Nat.Coprime 2 3) (⟨t, ht⟩ : H)
    have hd : orderOf (⟨t, ht⟩ : H) ∣ 3 :=
      orderOf_dvd_of_pow_eq_one (show (⟨t, ht⟩ : H) ^ 3 = 1 from Subtype.ext h)
    have he : (⟨t, ht⟩ : H) = 1 :=
      orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes hc (dvd_refl _) hd)
    exact (htn (congrArg Subtype.val he)).elim

lemma AuxiliaryModule.exists_small_reflection (b : AuxiliaryModule source i d)
    {E : Subgroup (FreeAmalgam R)} (estimates : SmallDisplacementData source i d E)
    (π : localFlagActor source (!i) d →* BinaryS3.Actor)
    (hk : π.ker = (localFlagKernel source (!i) d).subgroupOf (localFlagActor source (!i) d))
    (ρ : Representation (ZMod 2) BinaryS3.Actor b.Space)
    (ha : ∀ g v, b.representation g v = ρ (π g) v) :
    ∃ t : BinaryS3.Actor, t ^ 2 = 1 ∧ t ≠ 1 ∧ Nat.card (BinaryS3.displacement ρ t) ≤ 2 := by
  let H := (E.subgroupOf (localFlagActor source (!i) d)).map π
  have hne : H ≠ ⊥ := by
    intro hbot
    apply estimates.escapes
    intro x hx
    let g : localFlagActor source (!i) d := ⟨x, estimates.actor hx⟩
    have hg : g ∈ π.ker := mem_bot.mp (hbot ▸ mem_map_of_mem π (show g ∈ E.subgroupOf _ from hx))
    rw [hk] at hg
    exact hg
  obtain ⟨t, ht, htn, htm⟩ := two_subgroup_reflection H (estimates.two.comap_subtype.map π) hne
  refine ⟨t, ht, htn, ?_⟩
  have hle : BinaryS3.displacement ρ t ≤ b.image ⁅Y source i d, E⁆ := by
    rw [b.descended_commutator_image π ρ ha E estimates.actor]
    rintro v ⟨w, rfl⟩
    exact Submodule.subset_span ⟨t, htm, w, Submodule.mem_top, rfl⟩
  have hc := Nat.card_le_card_of_injective (Submodule.inclusion hle) (Submodule.inclusion_injective hle)
  have hYE : ⁅Y source i d, E⁆ ≤ Y source i d :=
    le_normalizer_iff_commutator_le_left.mp (estimates.actor.trans (Y_normalized source i d))
  rw [b.image_card _ hYE] at hc
  exact hc.trans estimates.small

/-- Lift the natural coordinates to the literal commutator factor. Both maps
are onto; the coordinate kernel and the full actor kernel remain exact. -/
lemma AuxiliaryModule.movingFactor_of_naturalMoving [Finite M]
    (b : AuxiliaryModule source i d) (geometry : Geometry R) (hlarge : 2 < geometry.b R)
    (π : localFlagActor source (!i) d →* BinaryS3.Actor) (hπ : Function.Surjective π)
    (hk : π.ker = (localFlagKernel source (!i) d).subgroupOf (localFlagActor source (!i) d))
    (ρ : Representation (ZMod 2) BinaryS3.Actor b.Space)
    (ha : ∀ g v, b.representation g v = ρ (π g) v) (n : NaturalMoving ρ) :
    Nonempty (MovingFactor source i d) := by
  let H := ⁅Y source i d, localFlagActor source (!i) d⁆ ⊔ secondFlagLayer source i d
  have hHY : H ≤ Y source i d := sup_le
    (le_normalizer_iff_commutator_le_left.mp (Y_normalized source i d)) (second_le_Y source i d)
  have hi := b.descended_moving_image π hπ ρ ha
  let q : H →* Multiplicative b.Space := b.projection.comp (inclusion hHY)
  have hq (x : H) : (q x).toAdd ∈ (movedSpace ρ).toSubmodule := by
    rw [← hi]
    exact (b.mem_image_iff H _).mpr ⟨inclusion hHY x, x.property, rfl⟩
  let f : H →* Multiplicative (movedSpace ρ).toSubmodule := {
    toFun x := Multiplicative.ofAdd ⟨(q x).toAdd, hq x⟩
    map_one' := by
      apply Multiplicative.ext
      apply Subtype.ext
      exact congrArg Multiplicative.toAdd q.map_one
    map_mul' x y := by
      apply Multiplicative.ext
      apply Subtype.ext
      exact congrArg Multiplicative.toAdd (q.map_mul x y) }
  have hf : Function.Surjective f := by
    intro v
    have hv : v.toAdd.val ∈ b.image H := by
      rw [hi]
      exact v.toAdd.property
    obtain ⟨x, hx, he⟩ := (b.mem_image_iff H _).mp hv
    refine ⟨⟨x, hx⟩, ?_⟩
    apply Multiplicative.ext
    exact Subtype.ext he
  have hfker : f.ker = (secondFlagLayer source i d).subgroupOf H := by
    ext x
    change f x = 1 ↔ (x : FreeAmalgam R) ∈ secondFlagLayer source i d
    have he : f x = 1 ↔ q x = 1 := by
      constructor
      · intro h
        exact congrArg (fun v : Multiplicative (movedSpace ρ).toSubmodule =>
          Multiplicative.ofAdd v.toAdd.val) h
      · intro h
        apply Multiplicative.ext
        apply Subtype.ext
        exact congrArg Multiplicative.toAdd h
    rw [he]
    change b.projection (inclusion hHY x) = 1 ↔ _
    rw [← MonoidHom.mem_ker, b.kernel]
    rfl
  let e := AddEquiv.toMultiplicative n.coordinates.toAddEquiv
  let c := e.toMonoidHom.comp f
  let p := n.marking.toMonoidHom.comp π
  have hpker : p.ker = (localFlagKernel source (!i) d).subgroupOf (localFlagActor source (!i) d) := by
    rw [MonoidHom.ker_comp_of_injective π n.marking.toMonoidHom n.marking.injective]
    exact hk
  refine ⟨⟨{ projection := p
             surjective := n.marking.surjective.comp hπ
             coordinates := c
             coordinates_surjective := e.surjective.comp hf
             kernel := ?_
             normalized := ?_
             action := ?_ }, hpker⟩⟩
  · exact (MonoidHom.ker_comp_of_injective f e.toMonoidHom e.injective).trans hfker
  · exact (le_inf (normalizer_commutator_ge_right _ _)
      (Incident.secondFlagLayer_normalized source geometry hlarge i d)).trans
      (normalizer_inf_normalizer_le_normalizer_sup _ _)
  · intro a x y hy
    change n.coordinates (f y).toAdd = (n.marking (π a)).val.mulVec (n.coordinates (f x).toAdd)
    rw [← n.action]
    congr 1
    apply Subtype.ext
    change (q y).toAdd = ρ (π a) (q x).toAdd
    rw [← ha]
    exact b.action a (inclusion hHY x) (inclusion hHY y) hy

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceFour.Flags.RankOne.BinaryAuxiliary.Moving
