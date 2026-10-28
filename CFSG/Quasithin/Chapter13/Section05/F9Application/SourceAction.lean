module

public import CFSG.Quasithin.Chapter13.Section05.PointAction
public import Theory.SpecificGroups.SymmetricSix.BinaryFlags.QuadraticPointCore
/-!
# The literal conjugate action in the F.9 application

The normalizer of L preserving the chosen natural module acts through
coordinate permutations on that same module. The 13.5.7 seed-commutator
antecedent places Vᵍ inside this normalizer, using the previously proved
point-fixer reduction of 13.5.5 and its precise 13.5.4 centralizer input.
The other commutator antecedent makes the actual Vᵍ action quadratic,
since all commutators lie in the abelian conjugate Vᵍ.

The source maps and ambient subgroups are retained. This constructs the
quadratic action; its point-core placement and the plane-fusion argument
remain the next source steps.

Source: Aschbacher--Smith, proof of 13.5.7, printed pp.917--918.
-/

@[expose] public section
open Subgroup BinaryPermutation
open scoped commutatorElement IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section05.QuadraticSource
open Section08.SourceCompletion Section07.NaturalAction
open Section08.TransvectionQuotients.FiveSeed.BarMarking
open Theory.SpecificGroups.SymmetricSix.BinaryFlags.QuadraticPointCore
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V V₁ V₂ V₃ M G₁ : Subgroup G}
  (d : NaturalSetup T L V V₁ V₂ V₃ M G₁)
noncomputable abbrev localModuleNormalizer := M ⊓ normalizer (V : Set G)
include d
theorem L_le_local : L ≤ localModuleNormalizer (M:=M) (V:=V) := by
  apply le_inf
  · rw [d.local_normalizer]
    exact L.le_normalizer
  · exact le_sup_left.trans d.normalizes_V

theorem local_permutation_extension :
    ∃ f : localModuleNormalizer (M:=M) (V:=V) →* Equiv.Perm (Fin 6),
      (∀l:L, f (inclusion (L_le_local d) l) = (d.local_quotient (QuotientGroup.mk' _ l)).val) ∧
      (∀ (g : localModuleNormalizer (M:=M) (V:=V)) (v:V),
        (d.coordinate (V.normalizerMonoidHom ⟨g.val,g.property.2⟩ v)).toAdd =
          naturalRepresentation (Fin 6) (f g) (d.coordinate v).toAdd) := by
  let := elementary d
  let α := d.local_quotient.toMonoidHom.comp (QuotientGroup.mk' _)
  have hα : Function.Surjective α := d.local_quotient.surjective.comp (QuotientGroup.mk'_surjective _)
  obtain ⟨f,hfL,hfV,_⟩ := natural_extension (localModuleNormalizer (M:=M) (V:=V)) L V
    (L_le_local d) (by rw [d.local_normalizer]; exact inf_le_left) inf_le_right
    α hα (linearCoordinate d) (fun l v => d.conjugation l v.toMul)
  exact ⟨f,hfL,fun g v=>hfV g (Additive.ofMul v)⟩

noncomputable def permutation : localModuleNormalizer (M:=M) (V:=V) →* Equiv.Perm (Fin 6) :=
  (local_permutation_extension d).choose

theorem conjugation (g : localModuleNormalizer (M:=M) (V:=V)) (v:V) :
    (d.coordinate (V.normalizerMonoidHom ⟨g.val,g.property.2⟩ v)).toAdd =
      naturalRepresentation (Fin 6) (permutation d g) (d.coordinate v).toAdd :=
  (local_permutation_extension d).choose_spec.2 g v

/-- Both displayed source commutator antecedents place the conjugate inside M_V. -/
theorem conjugate_le_local (g:G) (hg:g∈G₁)
    (hcentral : centralizer (V₃:Set G) ≤ localModuleNormalizer (M:=M) (V:=V))
    (hseed : ⁅V₃,V.map (MulAut.conj g).toMonoidHom⁆ ≤ V₁) :
    V.map (MulAut.conj g).toMonoidHom ≤ localModuleNormalizer (M:=M) (V:=V) := by
  have hVT : V≤(T:Subgroup G) := d.chosen.le_sylow
  have hTG : (T:Subgroup G)≤G₁ := by rw [d.first_normalizer];exact d.line_stable
  have hA : V.map (MulAut.conj g).toMonoidHom ≤ G₁ := by
    rintro _ ⟨v,hv,rfl⟩
    exact G₁.mul_mem (G₁.mul_mem hg (hTG (hVT hv))) (G₁.inv_mem hg)
  have hn : V.map (MulAut.conj g).toMonoidHom ≤ normalizer (V₃:Set G) :=
    le_normalizer_iff_commutator_le_left.mpr (hseed.trans (d.line_le_plane.trans d.plane_le_seed))
  exact (le_inf hA hn).trans (PointAction.normalizer_intersection_source d hcentral)

/-- The literal action of any conjugate known to lie in M_V. -/
noncomputable def conjugateAction (g:G)
    (h : V.map (MulAut.conj g).toMonoidHom ≤ localModuleNormalizer (M:=M) (V:=V)) :
    V.map (MulAut.conj g).toMonoidHom →* Equiv.Perm (Fin 6) :=
  (permutation d).comp (inclusion h)

theorem conjugate_quadratic (g:G)
    (h : V.map (MulAut.conj g).toMonoidHom ≤ localModuleNormalizer (M:=M) (V:=V))
    (hc : ⁅V,V.map (MulAut.conj g).toMonoidHom⁆ ≤ V.map (MulAut.conj g).toMonoidHom) :
    Quadratic (conjugateAction d g h).range := by
  let A := V.map (MulAut.conj g).toMonoidHom
  let := elementary d
  let : IsElementaryAbelian 2 A := IsElementaryAbelian.map _
  rintro _ ⟨x,rfl⟩ _ ⟨y,rfl⟩ w
  obtain ⟨v,hv⟩ := d.coordinate.surjective (Multiplicative.ofAdd w)
  have hw : (d.coordinate v).toAdd = w := congrArg Multiplicative.toAdd hv
  rw [← hw]
  let c : V := V.normalizerMonoidHom ⟨y.val,(h y.property).2⟩ v * v⁻¹
  have hd : naturalRepresentation (Fin 6) (conjugateAction d g h y) (d.coordinate v).toAdd -
      (d.coordinate v).toAdd = (d.coordinate c).toAdd := by
    rw [show conjugateAction d g h y = permutation d (inclusion h y) from rfl,
      ← conjugation d]
    change _ = (d.coordinate (V.normalizerMonoidHom _ v * v⁻¹)).toAdd
    rw [map_mul,map_inv,toAdd_mul,toAdd_inv,sub_eq_add_neg]
    rfl
  rw [hd]
  have hcA : c.val∈A := by
    apply hc
    rw [commutator_comm]
    exact commutator_mem_commutator y.property v.property
  have hcomm : x.val*c.val = c.val*x.val :=
    congrArg (fun a:A=>a.val) (mul_comm x ⟨c.val,hcA⟩)
  have hfix : V.normalizerMonoidHom ⟨x.val,(h x.property).2⟩ c = c := by
    apply Subtype.ext
    change x.val*c.val*x.val⁻¹=c.val
    rw [hcomm,mul_inv_cancel_right]
  change naturalRepresentation (Fin 6) (permutation d (inclusion h x)) (d.coordinate c).toAdd = _
  rw [← conjugation d]
  exact congrArg (fun v:V=>(d.coordinate v).toAdd) hfix

/-- The original 13.5.7 antecedents give the actual marked quadratic action. -/
theorem conjugate_quadratic_source (g:G) (hg:g∈G₁)
    (hcentral : centralizer (V₃:Set G) ≤ localModuleNormalizer (M:=M) (V:=V))
    (hcomm : ⁅V,V.map (MulAut.conj g).toMonoidHom⁆ ≤ V ⊓ V.map (MulAut.conj g).toMonoidHom)
    (hseed : ⁅V₃,V.map (MulAut.conj g).toMonoidHom⁆ ≤ V₁) :
    Quadratic (conjugateAction d g (conjugate_le_local d g hg hcentral hseed)).range :=
  conjugate_quadratic d g _ (hcomm.trans inf_le_right)
end CFSG.Quasithin.Chapter13.Section05.QuadraticSource
