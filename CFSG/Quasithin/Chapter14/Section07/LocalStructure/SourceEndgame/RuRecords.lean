module

public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.SourceEndgame.SourceMarking
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.SourceEndgame.CanonicalCover
public import Theory.Representation.PSL3Two.NaturalSylowFixed
public import Theory.GroupTheory.InvolutionCentralizerControl
public import Theory.GroupTheory.ConjugateSpanSylow

/-!
# Literal Ru interfaces from the local source conclusions

Characteristic two places Z(T) inside Z(O₂(L)) = V. The marked natural
Sylow action bounds this center by two, while the actual flag point lies
in it; hence Z(T) = V₁. This uses T ≤ L, supplied by 14.7.74.

U₀ = V₁ makes the original projection on U/V₁ injective, constructing the
full S₅ natural section. Its overgroup and conjugate span agree with the
literal Ru2 groups. The Ru1 constructor transports a proved Steinberg
equivalence using the same qL as the original natural section, and derives
the required normalizer equality from proved 14.7.67(5).

These are conditional assembly results. The special-group equalities,
Steinberg recognition and T ≤ L must still be proved by 14.7.71–74; the
canonical Ru2 constructor additionally needs its marked root/quotient inputs.
Source: Aschbacher–Smith 14.7.72–75 and J.1, printed pp.1076–1078 and 431,
combined manuscript of 1 March 2004.
-/

public section

open Subgroup Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.SourceEndgame
open Chapter12.Section08 CriticalFusion.Source ChapterJ
universe u
variable {G : Type u} [Group G] [Finite G]
  {T : Sylow 2 G} {L V : Subgroup G} {F : InvariantFlag T V 3}
  {W : Type u} [AddCommGroup W] [Module (ZMod 2) W] (d : Data T L V F W)

include d in
theorem source_sylowCenter_eq_point
    (hTL : (T : Subgroup G) ≤ L)
    (hchar : L ⊓ centralizer (L.pCoreIn 2 : Set G) ≤ L.pCoreIn 2)
    (hcenter : (center (L.pCoreIn 2)).map (L.pCoreIn 2).subtype = V) :
    sylowCenter T = F.Vi 1 := by
  have hST : L.pCoreIn 2 ≤ (T : Subgroup G) := by
    have hh := pCoreIn_le_sylow L (T.subtype hTL)
    simpa only [Sylow.coe_subtype, map_subgroupOf_eq_of_le hTL] using hh
  have hZT : sylowCenter T ≤ (T : Subgroup G) := map_subtype_le _
  have hZC : sylowCenter T ≤ centralizer (T : Set G) := by
    rintro z ⟨x,hx,rfl⟩ t ht
    exact congrArg Subtype.val (mem_center_iff.mp hx ⟨t,ht⟩)
  have hZS : sylowCenter T ≤ L.pCoreIn 2 :=
    (le_inf (hZT.trans hTL) (hZC.trans (centralizer_le hST))).trans hchar
  have hZV : sylowCenter T ≤ V := by
    rw [← hcenter]
    intro z hz
    refine ⟨⟨z,hZS hz⟩, ?_, rfl⟩
    apply mem_center_iff.mpr
    intro s
    exact Subtype.ext (hZC hz s (hST s.property))
  let P := (T.subtype hTL).mapSurjective d.qL_surjective
  let f : sylowCenter T → fixedSpace BinaryLinearThree.W (P : Subgroup _) := fun z =>
    ⟨(d.naturalCoordinates ⟨z,hZV z.property⟩).toAdd, by
      intro p
      obtain ⟨t,ht,he⟩ := p.property
      have hh := d.naturalCoordinates_equivariant t ⟨z,hZV z.property⟩
      change BinaryLinearThree.W p.val _ = _
      rw [← he, ← hh]
      congr 2
      apply Subtype.ext
      change (t : G) * (z : G) * (t : G)⁻¹ = z
      rw [hZC z.property t ht, mul_inv_cancel_right]⟩
  have hf : Function.Injective f := by
    intro x y h
    have hh := d.naturalCoordinates_bijective.1 (congrArg (fun x => Multiplicative.ofAdd x.val) h)
    exact Subtype.ext (congrArg (fun v : V => (v : G)) hh)
  have hbound : Nat.card (sylowCenter T) ≤ 2 :=
    (Nat.card_le_card_of_injective f hf).trans (BinaryLinearThree.card_sylow_natural_fixed_le_two P)
  have hpoint : Nat.card (F.Vi 1) = 2 := by simpa using F.card 1 (by decide)
  have hPT : F.Vi 1 ≤ (T : Subgroup G) := (F.le_seed 1).trans d.natural.chosen.le_sylow
  have hPC : (T : Subgroup G) ≤ centralizer (F.Vi 1 : Set G) :=
    (F.invariant 1).trans (normalizer_le_centralizer_of_card_two (F.Vi 1) hpoint)
  have hPZ : F.Vi 1 ≤ sylowCenter T := by
    intro z hz
    refine ⟨⟨z,hPT hz⟩, ?_, rfl⟩
    apply mem_center_iff.mpr
    intro t
    exact Subtype.ext (hPC t.property z hz).symm
  exact (eq_of_le_of_card_ge hPZ (by simpa only [hpoint] using hbound)).symm

end CFSG.Quasithin.Chapter14.Section07.LocalStructure.SourceEndgame

open Subgroup Representation
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.SourceEndgame
open Chapter12.Section08 CriticalFusion.Source ChapterJ
universe u
variable {G : Type u} [Group G] [Finite G]
  {T : Sylow 2 G} {L V : Subgroup G} {F : InvariantFlag T V 3}
  {W : Type u} [AddCommGroup W] [Module (ZMod 2) W] (d : Data T L V F W)

theorem source_projection_injective (hpoint : d.U₀ = F.Vi 1) :
    Function.Injective d.projection := by
  apply LinearMap.ker_eq_bot.mp
  apply bot_unique
  intro w hw
  obtain ⟨x,hx⟩ := d.conjugationSection.onto (Multiplicative.ofAdd w)
  have hx' : (d.conjugationSection.coordinates x).toAdd = w := congrArg Multiplicative.toAdd hx
  have hxu : (x : G) ∈ d.U₀ := (d.mem_U₀ x).mpr (hx'.symm ▸ hw)
  rw [hpoint] at hxu
  exact hx' ▸ (d.conjugationSection.coordinates_eq_one_iff x).mpr hxu

/-- The original U/V₁ is natural once its fixed kernel vanishes. -/
noncomputable def source_natural_U_section (hpoint : d.U₀ = F.Vi 1) :
    BinaryConjugationSection F.H F.U (F.Vi 1) (d.naturalQuotient.action.comp d.qH) where
  section_le := d.conjugationSection.section_le
  kernel_le := d.conjugationSection.kernel_le
  normalized := d.conjugationSection.normalized
  coordinates := d.projection.toLinearMap.toAddMonoidHom.toMultiplicative.comp
    d.conjugationSection.coordinates
  onto := d.projection_onto.comp d.conjugationSection.onto
  kernel_eq := by
    ext x
    change d.projection (d.conjugationSection.coordinates x).toAdd = 0 ↔ (x : G) ∈ F.Vi 1
    have hinj : Function.Injective d.projection.toLinearMap := source_projection_injective d hpoint
    change d.projection.toLinearMap _ = 0 ↔ _
    rw [← d.projection.toLinearMap.map_zero, hinj.eq_iff]
    exact d.conjugationSection.coordinates_eq_one_iff x
  equivariant := by
    intro h x
    change d.projection (d.conjugationSection.coordinates _).toAdd = _
    rw [d.conjugationSection.equivariant]
    exact LinearMap.congr_fun (d.projection.isIntertwining' h) _

theorem source_ruOne_of_steinberg
    (earlier : d.ModuleSeparation) (hTL : (T : Subgroup G) ≤ L)
    (hcenter : (center (L.pCoreIn 2)).map (L.pCoreIn 2).subtype = V)
    (hPhi : (frattini (L.pCoreIn 2)).map (L.pCoreIn 2).subtype = V)
    (hderived : (commutator (L.pCoreIn 2)).map (L.pCoreIn 2).subtype = V)
    {M : Type*} [AddCommGroup M] [Module (ZMod 2) M]
    (ρ : Representation (ZMod 2) BinaryLinearThree.Group M)
    (s : BinaryConjugationSection L (L.pCoreIn 2) V (ρ.comp d.qL))
    (e : Representation.Equiv ρ BinaryLinearThree.S) : Nonempty (RuOne L V) := by
  let c : L.pCoreIn 2 →* Multiplicative BinaryLinearThree.Steinberg :=
    e.toLinearEquiv.toAddEquiv.toMultiplicative.toMonoidHom.comp s.coordinates
  have hc : c.ker = V.subgroupOf (L.pCoreIn 2) := by
    ext x
    change e (s.coordinates x).toAdd = 0 ↔ (x : G) ∈ V
    change e.toLinearEquiv _ = 0 ↔ _
    rw [e.toLinearEquiv.map_eq_zero_iff]
    exact s.coordinates_eq_one_iff x
  refine ⟨{
    normalizer_eq := ?_
    center_eq := hcenter
    frattini_eq := hPhi
    derived_eq := hderived
    quotientMap := d.qL
    quotient_surjective := d.qL_surjective
    quotient_kernel := d.qL_ker
    natural := d.natural_section (s.kernel_le.trans s.section_le)
    steinberg := {
      section_le := s.section_le
      kernel_le := s.kernel_le
      normalized := s.normalized
      coordinates := c
      onto := e.toLinearEquiv.surjective.comp s.onto
      kernel_eq := hc
      equivariant := ?_ } }⟩
  · simpa only [sup_eq_left.mpr hTL] using d.lemma_14_7_67_five earlier
  · intro l x
    change e (s.coordinates _).toAdd = _
    rw [s.equivariant]
    exact LinearMap.congr_fun (e.isIntertwining' (d.qL l)) _

include d in
/-- Identify the literal Ru2 overgroup from the original centralizer of z. -/
theorem source_H_eq_RuTwo_overgroup (hz : sylowCenter T = F.Vi 1) :
    F.H = centralizerOfSylowCenter T := by
  unfold centralizerOfSylowCenter
  rw [hz, d.point, zpowers_eq_closure, centralizer_closure]
  exact d.centralizer_eq

omit [Finite G] in
/-- The two source conventions for the conjugate span agree. -/
theorem source_U_eq_RuTwo_span : F.U = conjugateSpan F.H V := by
  exact conjugateSpanBy_eq_iSup_conj V F.H

/-- The full S₅ natural section on the literal Ru2 groups. No action-descent
or zero-kernel premise is retained after U₀=V₁ has been proved. -/
theorem source_RuTwo_natural_data (hpoint : d.U₀ = F.Vi 1)
    (hz : sylowCenter T = F.Vi 1) :
    ∃ q : centralizerOfSylowCenter T →* S5,
      Function.Surjective q ∧
      q.ker = ((centralizerOfSylowCenter T).pCoreIn 2).subgroupOf
        (centralizerOfSylowCenter T) ∧
      Nonempty (BinaryConjugationSection (centralizerOfSylowCenter T)
        (conjugateSpan (centralizerOfSylowCenter T) V) (sylowCenter T)
        (d.naturalQuotient.action.comp q)) := by
  rw [← source_H_eq_RuTwo_overgroup d hz, hz, ← source_U_eq_RuTwo_span (F := F)]
  exact ⟨d.qH,d.qH_surjective,d.qH_ker,⟨source_natural_U_section d hpoint⟩⟩

end CFSG.Quasithin.Chapter14.Section07.LocalStructure.SourceEndgame
