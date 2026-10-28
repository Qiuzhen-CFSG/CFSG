module

public import CFSG.Quasithin.Chapter13.Section07.NaturalAction
public import CFSG.Quasithin.Chapter13.Section05.Preliminaries
public import Theory.SpecificGroups.SymmetricSix.BinaryFlags.PointAction.Transport
/-!
# The source point-fixer action and normalizer intersection

The original natural coordinates identify the source seed V₃ with the
perpendicular of its order-two line V₁. Every automorphism of the seed
fixing that line is induced by an actual element of L. Thus the earlier
ambient centralizer bound from 13.5.4(4) gives 13.5.5, and the literal H_z
consumer yields the strict seed inclusion 13.5.9.

Only that earlier centralizer bound remains explicit in the last two
statements. The point-fixer action is constructed from NaturalSetup.
Source: Aschbacher--Smith, 13.5.5 and 13.5.9, printed pp.916 and 918.
-/

@[expose] public section
open Subgroup BinaryPermutation
namespace CFSG.Quasithin.Chapter13.Section05.PointAction
open Section08.SourceCompletion Section07.NaturalAction
open Theory.SpecificGroups.SymmetricSix.BinaryFlags.NaturalPairing
open Theory.SpecificGroups.SymmetricSix.BinaryFlags.PointAction
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V V₁ V₂ V₃ M G₁ : Subgroup G}
  (d : NaturalSetup T L V V₁ V₂ V₃ M G₁)

private noncomputable def seedCoordinates : V₃ ≃* Multiplicative (image d V₃) := by
  let f : V₃ →* Multiplicative (image d V₃) := {
    toFun := fun x => Multiplicative.ofAdd
      ⟨(d.coordinate ⟨x.val,d.seed_le x.property⟩).toAdd,
        (mem_image d V₃ _).mpr ⟨⟨x.val,d.seed_le x.property⟩,x.property,rfl⟩⟩
    map_one' := by
      apply Multiplicative.toAdd.injective
      apply Subtype.ext
      exact d.coordinate.map_one
    map_mul' := fun a b => by
      apply Multiplicative.toAdd.injective
      apply Subtype.ext
      change d.coordinate ⟨(a*b).val, d.seed_le (mul_mem a.property b.property)⟩ =
        d.coordinate ⟨a.val,d.seed_le a.property⟩ * d.coordinate ⟨b.val,d.seed_le b.property⟩
      exact d.coordinate.map_mul ⟨a.val,d.seed_le a.property⟩ ⟨b.val,d.seed_le b.property⟩ }
  exact MulEquiv.ofBijective f ⟨by
    intro a b hab
    apply Subtype.ext
    have hh := congrArg (fun v:Multiplicative (image d V₃) => Multiplicative.ofAdd v.toAdd.val) hab
    exact congrArg (fun x:V=>x.val) (d.coordinate.injective hh), by
    intro y
    obtain ⟨v,hv,he⟩ := (mem_image d V₃ _).mp y.toAdd.property
    refine ⟨⟨v.val,hv⟩,?_⟩
    apply Multiplicative.toAdd.injective
    exact Subtype.ext he⟩

private theorem image_line (z : V₁) (hz : z ≠ 1) :
    image d V₁ = Submodule.span (ZMod 2)
      {(d.coordinate ⟨z.val,d.line_le_plane.trans (d.plane_le_seed.trans d.seed_le) z.property⟩).toAdd} := by
  have hline : V₁ ≤ V := d.line_le_plane.trans (d.plane_le_seed.trans d.seed_le)
  apply eq_span_singleton_of_mem_of_finrank_eq_one
    (image_dim d V₁ hline 1 d.line_card)
  · exact (mem_image d V₁ _).mpr ⟨⟨z.val,hline z.property⟩,z.property,rfl⟩
  · intro he
    apply hz
    apply Subtype.ext
    exact congrArg (fun x:V=>x.val) (d.coordinate.injective (he.trans d.coordinate.map_one.symm))

include d in
theorem source_action (a : MulAut V₃)
    (ha : ∀v:V₃,v.val ∈ V₁ → a v = v) :
    ∃l∈L, ∀v:V₃,(a v).val = l*v.val*l⁻¹ := by
  let : Nontrivial V₁ := Finite.one_lt_card_iff_nontrivial.mp (by rw [d.line_card];decide)
  obtain ⟨z,hz⟩ := exists_ne (1:V₁)
  have hzV : z.val ∈ V := d.seed_le (d.plane_le_seed (d.line_le_plane z.property))
  let v := (d.coordinate ⟨z.val,hzV⟩).toAdd
  have hv : v ≠ 0 := by
    intro h
    apply hz
    apply Subtype.ext
    exact congrArg (fun x:V=>x.val) (d.coordinate.injective (h.trans d.coordinate.map_one.symm))
  have himage : image d V₃ = Perpendicular v := by
    rw [seed_perpendicular d,image_line d z hz]
  let e : V₃ ≃* Multiplicative (Perpendicular v) := (seedCoordinates d).trans
    (LinearEquiv.ofEq (image d V₃) (Perpendicular v) himage).toAddEquiv.toMultiplicative
  have heval (w:V₃) : (e w).toAdd.val =
      (d.coordinate ⟨w.val,d.seed_le w.property⟩).toAdd := rfl
  let z3 : V₃ := ⟨z.val,d.plane_le_seed (d.line_le_plane z.property)⟩
  have hez : e z3 = perpendicularPoint v := by
    apply Multiplicative.toAdd.injective
    exact Subtype.ext rfl
  let b := (MulAut.congr e) a
  have hb : b (perpendicularPoint v) = perpendicularPoint v := by
    rw [← hez]
    change e (a (e.symm (e z3))) = e z3
    rw [e.symm_apply_apply,ha z3 z.property]
  obtain ⟨g,hgv,hg⟩ := exists_even_action v hv b hb
  obtain ⟨q,hq⟩ := d.local_quotient.surjective g
  obtain ⟨l,hl⟩ := QuotientGroup.mk'_surjective _ q
  refine ⟨l.val,l.property,?_⟩
  intro w
  have hact := hg (e w)
  change (e (a (e.symm (e w)))).toAdd.val = _ at hact
  rw [e.symm_apply_apply,heval,heval] at hact
  have hc := d.conjugation l ⟨w.val,d.seed_le w.property⟩
  rw [hl,hq] at hc
  have he := d.coordinate.injective (hact.trans hc.symm)
  exact congrArg Subtype.val he

include d in
theorem normalizer_intersection_source
    (hcentral : centralizer (V₃ : Set G) ≤ M ⊓ normalizer (V : Set G)) :
    G₁ ⊓ normalizer (V₃ : Set G) ≤ M ⊓ normalizer (V : Set G) := by
  rw [d.first_normalizer]
  apply normalizer_intersection_le_of_point_fixer_action V₁ V₃ L
    (M ⊓ normalizer (V : Set G)) d.line_card
  · apply le_inf
    · rw [d.local_normalizer]
      exact L.le_normalizer
    · exact le_sup_left.trans d.normalizes_V
  · exact hcentral
  · exact source_action d

include d in
theorem seed_lt_source (L₁ H : Subgroup G)
    (hcentral : centralizer (V₃ : Set G) ≤ M ⊓ normalizer (V : Set G))
    (hH : H ∈ Section08.Source.Hz L₁ T G₁ M) :
    V₃ < Section08.Source.UH H V₃ := by
  apply seed_lt_UH_of_mem_Hz L₁ T V₁ V₃ M H
  · simpa only [d.first_normalizer] using hH
  · simpa only [d.first_normalizer] using (normalizer_intersection_source d hcentral).trans inf_le_left

end CFSG.Quasithin.Chapter13.Section05.PointAction
