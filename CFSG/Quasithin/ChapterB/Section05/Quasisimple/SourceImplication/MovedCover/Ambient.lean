module
public import CFSG.Quasithin.ChapterB.Section05.Quasisimple.SourceImplication.MovedCover.Elementary

/-!
# The ambient action of a marked moved cover

The component equivalence of a moved quotient supplies coordinates for the
whole ambient action on that quotient. A normal component with trivial
centralizer makes the full quotient action faithful whenever its component
action is faithful. The original quotient homomorphism transports to every
embedded vertex group with its exact kernel and component image retained;
the cover projection and embedding preserve the actual conjugation action.

Source: MS93 (3.2)(vi) and (3.3), pp.866–867. This is the ambient marking
needed before excluding outer actors from the critical plane centralizer.
-/

@[expose] public noncomputable section
open Subgroup Representation Representation.BinaryOffender Representation.OneCohomology
namespace CFSG.Quasithin.ChapterB.QuasisimpleSource.MovedSection
variable {G D V W : Type*} [Group G] [Group D]
  [AddCommGroup V] [Module (ZMod 2) V] [AddCommGroup W] [Module (ZMod 2) W]
  {ρ : Representation (ZMod 2) G V} {τ : Representation (ZMod 2) D W}
  {L : Subgroup G}

/-- The whole ambient action in the specified natural-section coordinates. -/
def ambientAction (s : MovedSection ρ L) (e : ActionEquiv (s.action.comp L.subtype) τ) :
    Representation (ZMod 2) G W :=
  e.linearEquiv.conjRingEquiv.toMonoidHom.comp s.action

theorem ambientAction_component (s : MovedSection ρ L)
    (e : ActionEquiv (s.action.comp L.subtype) τ) (g : L) (w : W) :
    ambientAction s e g w = τ (e.groupEquiv g) w := by
  change e.linearEquiv ((MovedSection.action ρ s) g (e.linearEquiv.symm w)) = _
  exact (e.intertwines g (e.linearEquiv.symm w)).trans (by rw [e.linearEquiv.apply_symm_apply])

theorem coverProjection_ambient (s : MovedSection ρ L)
    (e : ActionEquiv (s.action.comp L.subtype) τ) (g : G) (v : s.space.toSubmodule) :
    coverProjection s e (s.space.toRepresentation g v) =
      ambientAction s e g (coverProjection s e v) := by
  change e.linearEquiv ((MovedSection.action ρ s) g (s.central.toSubmodule.mkQ v)) =
    e.linearEquiv ((MovedSection.action ρ s) g (e.linearEquiv.symm (e.linearEquiv (s.central.toSubmodule.mkQ v))))
  rw [e.linearEquiv.symm_apply_apply]

/-- A representation faithful on a normal subgroup with trivial centralizer
is faithful on the entire ambient group. -/
theorem faithful_of_faithful_centric_restriction
    (ψ : Representation (ZMod 2) G W) [L.Normal]
    (hL : Function.Injective (ψ.comp L.subtype))
    (hcent : centralizer (L : Set G) = ⊥) : Function.Injective ψ := by
  apply (ψ.ker_eq_bot_iff).mp
  apply bot_unique
  intro x hx
  change x = 1
  have hc : x ∈ centralizer (L : Set G) := by
    intro y hy
    have he : (MulAut.conjNormal x : MulAut L) ⟨y,hy⟩ = ⟨y,hy⟩ := by
      apply hL
      change ψ (x * y * x⁻¹) = ψ y
      have hx' : ψ x = 1 := hx
      have hi : ψ x⁻¹ = 1 := by
        have hh := ψ.map_mul x⁻¹ x
        rw [inv_mul_cancel, map_one, hx', mul_one] at hh
        exact hh.symm
      rw [map_mul,map_mul,hx',hi,one_mul,mul_one]
    have he' : x * y * x⁻¹ = y := congrArg Subtype.val he
    exact (mul_inv_eq_iff_eq_mul.mp he').symm
  exact show x ∈ (⊥ : Subgroup G) from hcent ▸ hc

theorem ambientAction_faithful (s : MovedSection ρ L)
    (e : ActionEquiv (s.action.comp L.subtype) τ) [L.Normal]
    (hτ : Function.Injective τ) (hcent : centralizer (L : Set G) = ⊥) :
    Function.Injective (ambientAction s e) := by
  apply faithful_of_faithful_centric_restriction (L := L) _ ?_ hcent
  intro g h he
  apply e.groupEquiv.injective
  apply hτ
  apply LinearMap.ext
  intro w
  have hh := DFunLike.congr_fun he w
  change ambientAction s e (g : G) w = ambientAction s e (h : G) w at hh
  rwa [ambientAction_component, ambientAction_component] at hh

end CFSG.Quasithin.ChapterB.QuasisimpleSource.MovedSection

namespace CFSG.Quasithin.ChapterB.QuasisimpleSource.ElementaryMovedCover
open scoped IsMulCommutative
variable {H J G : Type*} [Group H] [Group J] [Group G]
  (X K : Subgroup H) [X.Normal] [IsElementaryAbelian 2 X]
  (q : H →* J) (hq : Function.Surjective q)
  (hker : q.ker = centralizer (X : Set H)) [(K.map q).Normal]
local notation "ρ" => NormalElementaryQuotient.representation X q hq hker
local notation "s" => MovedSection.ofNormal ρ (K.map q)

/-- The original ambient quotient transported onto its embedded vertex group. -/
def embeddedQuotient (i : H →* G) (hi : Function.Injective i)
    (B : Subgroup G) (hB : i.range = B) : B →* J :=
  q.comp ((MonoidHom.ofInjective hi).trans (MulEquiv.subgroupCongr hB)).symm.toMonoidHom

omit X K hq hker in
theorem embeddedQuotient_surjective (i : H →* G) (hi : Function.Injective i)
    (B : Subgroup G) (hB : i.range = B) (hq : Function.Surjective q) :
    Function.Surjective (embeddedQuotient q i hi B hB) :=
  hq.comp (((MonoidHom.ofInjective hi).trans (MulEquiv.subgroupCongr hB)).symm.surjective)

omit X K hq hker in
theorem embeddedQuotient_kernel (i : H →* G) (hi : Function.Injective i)
    (B : Subgroup G) (hB : i.range = B) :
    (embeddedQuotient q i hi B hB).ker.map B.subtype = q.ker.map i := by
  let d := (MonoidHom.ofInjective hi).trans (MulEquiv.subgroupCongr hB)
  have hd (b : B) : i (d.symm b) = (b : G) :=
    congrArg Subtype.val (d.apply_symm_apply b)
  ext x
  constructor
  · rintro ⟨b,hb,rfl⟩
    exact ⟨d.symm b, hb, hd b⟩
  · rintro ⟨y,hy,rfl⟩
    refine ⟨d y, ?_, rfl⟩
    change q (d.symm (d y)) = 1
    rwa [d.symm_apply_apply]

omit X K hq hker in
theorem embeddedQuotient_subgroup (i : H →* G) (hi : Function.Injective i)
    (B : Subgroup G) (hB : i.range = B) (K : Subgroup H) :
    ((K.map i).subgroupOf B).map (embeddedQuotient q i hi B hB) = K.map q := by
  let d := (MonoidHom.ofInjective hi).trans (MulEquiv.subgroupCongr hB)
  have hd (b : B) : i (d.symm b) = (b : G) :=
    congrArg Subtype.val (d.apply_symm_apply b)
  ext x
  constructor
  · rintro ⟨b,⟨y,hy,he⟩,rfl⟩
    refine ⟨y,hy,?_⟩
    have hh : y = d.symm b := hi (he.trans (hd b).symm)
    rw [hh]
    rfl
  · rintro ⟨y,hy,rfl⟩
    refine ⟨d y, ⟨y,hy,rfl⟩, ?_⟩
    change q (d.symm (d y)) = q y
    rw [d.symm_apply_apply]

/-- The full vertex action on the embedded moved cover is literal conjugation. -/
theorem embedded_ambient_conjugate (i : H →* G) (hi : Function.Injective i)
    (B : Subgroup G) (hB : i.range = B) (b : B) (v : (s).space.toSubmodule) :
    i (embedding X K q hq hker (Multiplicative.ofAdd
      ((s).space.toRepresentation (embeddedQuotient q i hi B hB b) v))) =
      (b : G) * i (embedding X K q hq hker (Multiplicative.ofAdd v)) * (b : G)⁻¹ := by
  let d := (MonoidHom.ofInjective hi).trans (MulEquiv.subgroupCongr hB)
  have hd : i (d.symm b) = (b : G) :=
    congrArg Subtype.val (d.apply_symm_apply b)
  have hh := congrArg i (embedding_conjugate X K q hq hker (d.symm b) v)
  simpa only [embeddedQuotient, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, d, map_mul,map_inv,hd] using hh

end CFSG.Quasithin.ChapterB.QuasisimpleSource.ElementaryMovedCover
