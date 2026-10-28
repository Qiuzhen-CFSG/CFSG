module
public import CFSG.Quasithin.ChapterB.Section05.Quasisimple.SourceImplication.Geometry
public import Theory.Representation.BinaryOffender.SharpSylowSupplement
public import Theory.Representation.BinaryOffender.NormalLayerQuotient
public import Theory.Representation.BinaryOffender.FixedQuotientKernel

/-!
# The whole natural quotient from its actual moved section

A faithful natural quotient of the actual moved submodule gives a faithful
ambient action on the same natural coordinates. Every original offender
therefore fills a defining Sylow subgroup. Equality in the offender bound,
followed by odd-index averaging, proves V=[V,L]+C_V(L). The original moved
central quotient is consequently equivariantly identical to V/C_V(L).
The same calculation puts every original best offender in L.
No splitting or whole-module recognition is an input.

Source: Aschbacher–Smith B.6.9 and E.2.3(1), pp.115–116 and216–217.
-/
public section
open Subgroup Representation Representation.BinaryOffender
namespace CFSG.Quasithin.ChapterB.QuasisimpleSource
variable {G V : Type*} [Group G] [Finite G]
  [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]

theorem moved_sup_fixed_of_natural_section
    (ρ : Representation (ZMod 2) G V) (hff : IsFFModule ρ)
    (L : Subgroup G) [L.Normal] (hself : centralizer (L : Set G) ≤ L)
    (s : MovedSection ρ L) (F : BinaryField) (hF : 2 < Nat.card F.Carrier)
    (e : ActionEquiv (s.action.comp L.subtype) (linearNatural F 2)) :
    moved ρ L ⊔ fixedSpace ρ L = ⊤ := by
  let f := e.linearEquiv.toLinearMap.comp s.central.toSubmodule.mkQ
  have hf : Function.Surjective f :=
    e.linearEquiv.surjective.comp s.central.toSubmodule.mkQ_surjective
  have hk : f.ker = fixedSpace s.space.toRepresentation L := by
    ext v
    change e.linearEquiv (s.central.toSubmodule.mkQ v) = 0 ↔ _
    rw [←e.linearEquiv.map_zero,e.linearEquiv.injective.eq_iff,
      Submodule.mkQ_apply,Submodule.Quotient.mk_eq_zero,s.central_eq]
  have he (g : L) v : f (s.space.toRepresentation (g:G) v) =
      linearNatural F 2 (e.groupEquiv g) (f v) := by
    exact e.intertwines g (s.central.toSubmodule.mkQ v)
  have hfaith : Function.Injective ((linearNatural F 2).comp e.groupEquiv.toMonoidHom) := by
    intro a b hab
    apply e.groupEquiv.injective
    apply Subtype.ext
    apply Matrix.ext_iff_mulVec.mpr
    intro v
    exact LinearMap.congr_fun hab v
  obtain ⟨τ,hτ,hfull,hnat⟩ := exists_faithful_action_of_normal_layer_quotient
    s.space.toRepresentation L hself ((linearNatural F 2).comp e.groupEquiv.toMonoidHom)
    hfaith f hf hk he
  obtain ⟨A,hA⟩ := hff
  obtain ⟨T,hAT⟩ := hA.1.2.isPGroup.exists_le_sylow
  rw [←s.space_eq]
  apply natural_layer_supplement_of_moved_section ρ s.space L e.groupEquiv τ hτ
    (fun g v => hnat g v) hF f hf hfull _ T A hA hAT
  intro g hg v
  change ρ g v - v ∈ s.space.toSubmodule
  rw [s.space_eq]
  exact Submodule.subset_span ⟨g,hg,v,Submodule.mem_top,rfl⟩

theorem whole_quotient_natural_of_moved_section
    (ρ : Representation (ZMod 2) G V) (hff : IsFFModule ρ)
    (L : Subgroup G) [L.Normal] (hself : centralizer (L : Set G) ≤ L)
    (s : MovedSection ρ L) (F : BinaryField) (hF : 2 < Nat.card F.Carrier)
    (e : ActionEquiv (s.action.comp L.subtype) (linearNatural F 2)) :
    Nonempty (ActionEquiv (fixedQuotientRepresentation ρ L) (linearNatural F 2)) := by
  have hsup := moved_sup_fixed_of_natural_section ρ hff L hself s F hF e
  rw [←s.space_eq] at hsup
  let C := fixedSpace ρ L
  let f : s.space.toSubmodule →ₗ[ZMod 2] V ⧸ C := C.mkQ.comp s.space.toSubmodule.subtype
  have hk : f.ker = s.central.toSubmodule := by
    ext w
    rw [s.central_eq]
    change C.mkQ (w:V) = 0 ↔ _
    rw [Submodule.mkQ_apply,Submodule.Quotient.mk_eq_zero]
    constructor
    · intro h g
      exact Subtype.ext (h g)
    · intro h g
      exact congrArg Subtype.val (h g)
  have hf : Function.Surjective f := by
    intro x
    obtain ⟨v,rfl⟩ := C.mkQ_surjective x
    obtain ⟨w,hw,z,hz,hv⟩ := Submodule.mem_sup.mp
      (hsup ▸ (Submodule.mem_top : v ∈ (⊤ : Submodule (ZMod 2) V)))
    refine ⟨⟨w,hw⟩,?_⟩
    change C.mkQ w = C.mkQ v
    rw [←hv,map_add]
    have hz0 : C.mkQ z = 0 := (Submodule.Quotient.mk_eq_zero C).mpr hz
    rw [hz0,add_zero]
  let Q : (s.space.toSubmodule ⧸ s.central.toSubmodule) ≃ₗ[ZMod 2] V ⧸ C :=
    (Submodule.quotEquivOfEq _ _ hk.symm).trans (f.quotKerEquivOfSurjective hf)
  have hQ (w : s.space.toSubmodule) : Q (s.central.toSubmodule.mkQ w) = C.mkQ (w:V) := rfl
  refine ⟨{groupEquiv := e.groupEquiv, linearEquiv := Q.symm.trans e.linearEquiv, intertwines := ?_}⟩
  intro g x
  obtain ⟨w,rfl⟩ := hf x
  change e.linearEquiv (Q.symm ((fixedQuotientRepresentation ρ L) g (f w))) =
    linearNatural F 2 (e.groupEquiv g) (e.linearEquiv (Q.symm (f w)))
  have h1 : Q.symm (f w) = s.central.toSubmodule.mkQ w := by
    apply Q.injective
    rw [Q.apply_symm_apply,hQ]
    rfl
  have h2 : Q.symm ((fixedQuotientRepresentation ρ L) g (f w)) =
      s.central.quotientRepresentation (g:G) (s.central.toSubmodule.mkQ w) := by
    apply Q.injective
    rw [Q.apply_symm_apply]
    change C.mkQ (ρ (g:G) (w:V)) = Q (s.central.toSubmodule.mkQ (s.space.toRepresentation (g:G) w))
    rw [hQ]
    rfl
  rw [h1,h2]
  exact e.intertwines g (s.central.toSubmodule.mkQ w)

theorem offenderSubgroup_le_natural_layer_of_moved_section
    (ρ : Representation (ZMod 2) G V)
    (L : Subgroup G) [L.Normal] (hself : centralizer (L : Set G) ≤ L)
    (s : MovedSection ρ L) (F : BinaryField) (hF : 2 < Nat.card F.Carrier)
    (e : ActionEquiv (s.action.comp L.subtype) (linearNatural F 2)) :
    offenderSubgroup ρ ≤ L := by
  let f := e.linearEquiv.toLinearMap.comp s.central.toSubmodule.mkQ
  have hf : Function.Surjective f :=
    e.linearEquiv.surjective.comp s.central.toSubmodule.mkQ_surjective
  have hk : f.ker = fixedSpace s.space.toRepresentation L := by
    ext v
    change e.linearEquiv (s.central.toSubmodule.mkQ v) = 0 ↔ _
    rw [←e.linearEquiv.map_zero,e.linearEquiv.injective.eq_iff,
      Submodule.mkQ_apply,Submodule.Quotient.mk_eq_zero,s.central_eq]
  have he (g : L) v : f (s.space.toRepresentation (g:G) v) =
      linearNatural F 2 (e.groupEquiv g) (f v) := by
    exact e.intertwines g (s.central.toSubmodule.mkQ v)
  have hfaith : Function.Injective ((linearNatural F 2).comp e.groupEquiv.toMonoidHom) := by
    intro a b hab
    apply e.groupEquiv.injective
    apply Subtype.ext
    apply Matrix.ext_iff_mulVec.mpr
    intro v
    exact LinearMap.congr_fun hab v
  obtain ⟨τ,hτ,hfull,hnat⟩ := exists_faithful_action_of_normal_layer_quotient
    s.space.toRepresentation L hself ((linearNatural F 2).comp e.groupEquiv.toMonoidHom)
    hfaith f hf hk he
  apply iSup_le
  intro A
  apply iSup_le
  rintro ⟨hA,_⟩
  have hAτ : IsOffender τ A := ⟨hA.1,
    (fixedCodim_le_of_equivariant_surjection s.space.toRepresentation τ f hf hfull A).trans
      ((fixedCodim_subrepresentation_le ρ s.space A).trans (hA.isOffender ρ).2)⟩
  obtain ⟨T,hAT⟩ := hA.1.2.isPGroup.exists_le_sylow
  exact ((SL2NaturalOffenders.Ratios.offender_iff_eq_sylowInf L e.groupEquiv τ
    (fun g v => hnat g v) hF hτ T hAT).mp hAτ).le.trans inf_le_right
end CFSG.Quasithin.ChapterB.QuasisimpleSource
