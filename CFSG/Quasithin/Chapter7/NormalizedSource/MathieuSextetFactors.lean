module
public import CFSG.Quasithin.Chapter7.NormalizedSource.MathieuSextetMovement
public import CFSG.Quasithin.ChapterH.Section13To16.CocodeLocal.Sextet.Layers
public import Theory.Representation.HexacodeAction.TerminalIrreducible
public import Theory.Representation.Quotient
public import Theory.Representation.SL2FourNaturalOrbits.BorelDualCore

/-!
# The actual residual factors of a marked sextet cocode

The native perfect sextet residual covers the full even hexacode group 3.A₆
and every even permutation of its six tetrads. Binary irreducibility of the
even hexacode action and duality prove irreducibility of the six-dimensional
middle factor on this residual. The alternating permutation action proves the
same for the four-dimensional top factor. The cubic center is retained on the
middle factor; it is not replaced by a centerless A₆ action.

A whole cocode marking restricts and descends to actual binary conjugation
sections with their specified subgroup denominators. The Chapter 12 consumer
NonFFSourceMathieuM24Factors constructs these sections for the original
V_z/⟨z⟩ and V/V_z. This supplies the module-factor inputs of source 8.2.11
and the irreducibility input of the normal-closure argument in 8.2.12.
The earlier whole-cocode marking and the remainder of 8.2.12–14 stay with
qt-d-1222-nonff-mathieu.

Source: Aschbacher–Smith H.15.3 and 8.2.11–12, printed pp.400,722,
refs/quasithin.pdf. The imported Golay and affine hexacode constructions are
by Gerald Höhn and ATLAS contributors, revision
8eabb35afe2b5e45bf913a2d05c53e558d2e2917, under the ATLAS Research and
Attribution License 1.0; see LICENSES/ATLAS.txt.
-/

public noncomputable section
open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
open Sporadic.Mathieu Sporadic.Mathieu.M24LocalGeometry MathieuCode
open MathieuCode.SextetLayers MathieuCode.SextetLayers.CoordinateTransport Atlas.Codes
open CFSG.Quasithin.ChapterH.Section13To16.CocodeLocal
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter7.NormalizedSource.MathieuSextet

private theorem native_residual_hex_image (S : Sextet) :
    (solvableResidual (sextetStabilizer S)).map (nativeQuotient S) = hexSign.ker := by
  rw [map_solvableResidual_eq _ (nativeQuotient_surjective S)]
  let : Group.IsPerfect HexEvenAutomorphisms := Hexacode.even_isPerfect
  apply le_antisymm
  · intro x hx
    have hm := map_solvableResidual_le hexSign (mem_map_of_mem hexSign hx)
    rw [solvableResidual_eq_bot] at hm
    exact hm
  · exact le_solvableResidual_of_isPerfect hexSign.ker

/-- A marking onto the native residual gives a surjection to the full even
hexacode cover, with its cubic center retained. -/
theorem marked_even_quotient {A : Type*} [Group A] (S : Sextet)
    (r : A →* sextetStabilizer S) (hr : r.range = solvableResidual (sextetStabilizer S)) :
    ∃ p : A →* HexEvenAutomorphisms, Function.Surjective p ∧
      ∀ x, (p x).val = nativeQuotient S (r x) := by
  let q := (nativeQuotient S).comp r
  have hq : q.range = hexSign.ker := by
    rw [MonoidHom.range_comp,hr,native_residual_hex_image]
  let p : A →* HexEvenAutomorphisms := q.codRestrict _ (fun x => by
    change q x ∈ hexSign.ker
    rw [←hq]
    exact ⟨x,rfl⟩)
  refine ⟨p,?_,fun _ => rfl⟩
  intro y
  obtain ⟨x,hx⟩ := (show y.val ∈ q.range from hq.symm ▸ y.property)
  exact ⟨x,Subtype.ext hx⟩

/-- The six-dimensional middle quotient stays irreducible for the actual
perfect residual, not merely for the whole sextet stabilizer. -/
private theorem middle_quotient_irreducible {A : Type*} [Group A] (S : Sextet)
    (r : A →* sextetStabilizer S) (hr : r.range = solvableResidual (sextetStabilizer S)) :
    IsIrreducible ((sextetLineInPair S).quotientRepresentation.comp r) := by
  obtain ⟨p,hp,hval⟩ := marked_even_quotient S r hr
  let e : RepEquiv ((sextetLineInPair S).quotientRepresentation.comp r)
      (Hexacode.evenAction.dual.comp p) := {
    toLinearEquiv := sextetMiddleModelEquiv S
    isIntertwining' := fun g => by
      apply LinearMap.ext
      intro v
      change sextetMiddleModelEquiv S ((sextetLineInPair S).quotientRepresentation (r g) v) = _
      rw [sextetMiddleModelEquiv_equivariant]
      apply LinearMap.ext
      intro w
      change (sextetMiddleModelEquiv S v) (Hexacode.action (nativeQuotient S ((r g)⁻¹)) w) =
        (sextetMiddleModelEquiv S v) (Hexacode.action ((p g)⁻¹).val w)
      rw [←map_inv r,←map_inv p,hval] }
  apply e.irreducible_of_euqiv
  apply (irreducible_comp_surjective_iff p hp _).mpr
  let : IsIrreducible Hexacode.evenAction := Hexacode.evenAction_isIrreducible
  exact SL2FourNatural.BorelDualCore.dual_irreducible _

/-- The native residual covers all even permutations of its actual six parts. -/
theorem residual_covers_even_parts (S : Sextet) (g : alternatingGroup (SextetPart S)) :
    ∃ x ∈ solvableResidual (sextetStabilizer S), sextetPartPerm S x = g.val := by
  let : Group.IsPerfect (alternatingGroup (SextetPart S)) :=
    ⟨commutator_alternatingGroup_eq_top (by rw [Nat.card_eq_fintype_card,card_sextetPart]; decide)⟩
  have hg := le_solvableResidual_of_isPerfect (alternatingGroup (SextetPart S)) g.property
  rw [←map_solvableResidual_eq (sextetPartPerm S) (nativePartPerm_surjective S)] at hg
  exact hg

/-- The four-dimensional top quotient is irreducible already on the residual. -/
private theorem top_quotient_irreducible {A : Type*} [Group A] (S : Sextet)
    (r : A →* sextetStabilizer S) (hr : r.range = solvableResidual (sextetStabilizer S)) :
    IsIrreducible ((sextetPairSubrepresentation S).quotientRepresentation.comp r) := by
  let σ := (sextetPairSubrepresentation S).quotientRepresentation.comp r
  let τ := BinaryPermutation.alternatingNaturalRepresentation (Ω := SextetPart S)
  let : IsIrreducible τ := BinaryPermutation.alternatingNatural_isIrreducible
    (by rw [card_sextetPart]; decide)
  let e := sextetTopModelEquiv S
  let : Nontrivial (BinaryPermutation.natural (SextetPart S)) :=
    Subrepresentation.irreducible_module_nontrivial τ
  let : Nontrivial (Cocode ⧸ (sextetPairSubrepresentation S).toSubmodule) :=
    (Equiv.nontrivial_congr e.toEquiv).mpr inferInstance
  refine ⟨fun P => ?_⟩
  let U : Subrepresentation τ := {
    toSubmodule := P.toSubmodule.map e.toLinearMap
    apply_mem_toSubmodule := by
      intro g v hv
      obtain ⟨w,hw,rfl⟩ := hv
      obtain ⟨s,hs,hsg⟩ := residual_covers_even_parts S g
      obtain ⟨x,rfl⟩ := (show s ∈ r.range from hr.symm ▸ hs)
      refine ⟨σ x w,P.apply_mem_toSubmodule x hw,?_⟩
      exact (sextetTopModelEquiv_equivariant S (r x) w).trans (by rw [hsg]; rfl) }
  rcases eq_bot_or_eq_top U with h | h
  · left
    apply Subrepresentation.toSubmodule_injective
    apply bot_unique
    intro v hv
    have hm : e v ∈ U := ⟨v,hv,rfl⟩
    rw [h] at hm
    exact e.injective ((show e v = 0 from hm).trans e.map_zero.symm)
  · right
    apply Subrepresentation.toSubmodule_injective
    apply top_unique
    intro v _
    have hm : e v ∈ U := by rw [h]; trivial
    obtain ⟨w,hw,he⟩ := hm
    exact e.injective he ▸ hw

/-- Actual cocode coordinates restrict to the seven-space and descend through
both literal denominators. These are conjugation sections, not dimension tags. -/
private theorem marked_quotient_sections {G : Type*} [Group G]
    (S : Sextet) (R W U Z : Subgroup G) [IsElementaryAbelian 2 W]
    (hWR : W ≤ R) (hRW : R ≤ normalizer (W : Set G))
    (hUW : U ≤ W) (hZU : Z ≤ U) (hRU : R ≤ normalizer (U : Set G))
    (r : R →* sextetStabilizer S) (F : Additive W ≃ₗ[ZMod 2] Cocode)
    (hF : ∀ (x : R) (w : W),
      F (Additive.ofMul (W.normalizerMonoidHom ⟨x,hRW x.property⟩ w)) =
        cocodeRepresentation (r x).val (F (Additive.ofMul w)))
    (hpair : ∀ w : W, (w : G) ∈ U ↔ F (Additive.ofMul w) ∈ sextetPairSpace S)
    (hline : ∀ w : W, (w : G) ∈ Z ↔ F (Additive.ofMul w) ∈ sextetTetradLine S) :
    Nonempty (BinaryConjugationSection R U Z
      ((sextetLineInPair S).quotientRepresentation.comp r)) ∧
    Nonempty (BinaryConjugationSection R W U
      ((sextetPairSubrepresentation S).quotientRepresentation.comp r)) := by
  let f : W →* Multiplicative Cocode := {
    toFun := fun w => Multiplicative.ofAdd (F (Additive.ofMul w))
    map_one' := F.map_zero
    map_mul' := fun x y => F.map_add (Additive.ofMul x) (Additive.ofMul y) }
  have hf : Function.Surjective f := fun v => by
    obtain ⟨w,hw⟩ := F.surjective v.toAdd
    exact ⟨w.toMul,hw⟩
  let u : U →* Multiplicative (sextetPairSubrepresentation S).toSubmodule := {
    toFun := fun x => Multiplicative.ofAdd
      ⟨F (Additive.ofMul (⟨x,hUW x.property⟩ : W)),(hpair _).mp x.property⟩
    map_one' := by apply Subtype.ext; exact F.map_zero
    map_mul' := fun x y => by
      apply Subtype.ext
      exact F.map_add (Additive.ofMul (⟨x,hUW x.property⟩ : W))
        (Additive.ofMul (⟨y,hUW y.property⟩ : W)) }
  have hu : Function.Surjective u := by
    intro v
    obtain ⟨w,hw⟩ := F.surjective v.toAdd.val
    have hwU : (w.toMul : G) ∈ U := (hpair _).mpr (hw.symm ▸ v.toAdd.property)
    exact ⟨⟨w.toMul,hwU⟩,Subtype.ext hw⟩
  constructor
  · refine ⟨{
      section_le := hUW.trans hWR
      kernel_le := hZU
      normalized := hRU
      coordinates := (sextetLineInPair S).toSubmodule.mkQ.toAddMonoidHom.toMultiplicative.comp u
      onto := (sextetLineInPair S).toSubmodule.mkQ_surjective.comp hu
      kernel_eq := ?_
      equivariant := ?_ }⟩
    · ext x
      change (sextetLineInPair S).toSubmodule.mkQ (u x).toAdd = 0 ↔ (x : G) ∈ Z
      rw [Submodule.mkQ_apply,Submodule.Quotient.mk_eq_zero]
      exact (hline (⟨x,hUW x.property⟩ : W)).symm
    · intro x v
      change (sextetLineInPair S).toSubmodule.mkQ _ =
        (sextetLineInPair S).toSubmodule.mkQ _
      apply congrArg (sextetLineInPair S).toSubmodule.mkQ
      apply Subtype.ext
      exact hF x (⟨v,hUW v.property⟩ : W)
  · refine ⟨{
      section_le := hWR
      kernel_le := hUW
      normalized := hRW
      coordinates := (sextetPairSpace S).mkQ.toAddMonoidHom.toMultiplicative.comp f
      onto := (sextetPairSpace S).mkQ_surjective.comp hf
      kernel_eq := ?_
      equivariant := ?_ }⟩
    · ext x
      change (sextetPairSpace S).mkQ (f x).toAdd = 0 ↔ (x : G) ∈ U
      rw [Submodule.mkQ_apply,Submodule.Quotient.mk_eq_zero]
      exact (hpair x).symm
    · intro x v
      change (sextetPairSpace S).mkQ _ = (sextetPairSpace S).mkQ _
      exact congrArg (sextetPairSpace S).mkQ (hF x v)

/-- The residual middle model is the dual of the actual conjugation action
on all native translations. The cubic scalar is retained. -/
@[expose] def middleAction {A : Type*} [Group A] (S : Sextet)
    (r : A →* sextetStabilizer S) :
    Representation (ZMod 2) A (Module.Dual (ZMod 2) hexacode) :=
  (nativeHexacodeRepresentation S).dual.comp r

/-- The top model is the actual natural permutation quotient on the six tetrads. -/
@[expose] def topAction {A : Type*} [Group A] (S : Sextet)
    (r : A →* sextetStabilizer S) :
    Representation (ZMod 2) A (BinaryPermutation.natural (SextetPart S)) :=
  (BinaryPermutation.naturalRepresentation (SextetPart S)).comp ((sextetPartPerm S).comp r)

private def middleEquiv {A : Type*} [Group A] (S : Sextet)
    (r : A →* sextetStabilizer S) :
    RepEquiv ((sextetLineInPair S).quotientRepresentation.comp r) (middleAction S r) := {
  toLinearEquiv := sextetMiddleModelEquiv S
  isIntertwining' := fun g => LinearMap.ext (sextetMiddleModelEquiv_equivariant S (r g)) }

private def topEquiv {A : Type*} [Group A] (S : Sextet)
    (r : A →* sextetStabilizer S) :
    RepEquiv ((sextetPairSubrepresentation S).quotientRepresentation.comp r) (topAction S r) := {
  toLinearEquiv := sextetTopModelEquiv S
  isIntertwining' := fun g => LinearMap.ext (sextetTopModelEquiv_equivariant S (r g)) }

/-- The residual middle model is irreducible. -/
theorem middle_residual_irreducible {A : Type*} [Group A] (S : Sextet)
    (r : A →* sextetStabilizer S) (hr : r.range = solvableResidual (sextetStabilizer S)) :
    IsIrreducible (middleAction S r) :=
  (middleEquiv S r).symm.irreducible_of_euqiv (middle_quotient_irreducible S r hr)

/-- The residual top model is irreducible. -/
theorem top_residual_irreducible {A : Type*} [Group A] (S : Sextet)
    (r : A →* sextetStabilizer S) (hr : r.range = solvableResidual (sextetStabilizer S)) :
    IsIrreducible (topAction S r) :=
  (topEquiv S r).symm.irreducible_of_euqiv (top_quotient_irreducible S r hr)

/-- Only the full translation kernel disappears from the middle action. -/
theorem middleAction_kernel {A : Type*} [Group A] (S : Sextet)
    (r : A →* sextetStabilizer S) :
    (middleAction S r).ker = (nativeQuotient S).ker.comap r := by
  change (nativeHexacodeRepresentation S).dual.ker.comap r = _
  rw [nativeHexacodeRepresentation_dual_kernel,nativeQuotient_kernel]

private def section_transport {G X Y : Type*} [Group G]
    [AddCommGroup X] [Module (ZMod 2) X] [AddCommGroup Y] [Module (ZMod 2) Y]
    {R W Z : Subgroup G} {ρ : Representation (ZMod 2) R X} {σ : Representation (ZMod 2) R Y}
    (d : BinaryConjugationSection R W Z ρ) (e : RepEquiv ρ σ) :
    BinaryConjugationSection R W Z σ where
  section_le := d.section_le
  kernel_le := d.kernel_le
  normalized := d.normalized
  coordinates := e.toLinearEquiv.toAddEquiv.toMultiplicative.toMonoidHom.comp d.coordinates
  onto := e.toLinearEquiv.surjective.comp d.onto
  kernel_eq := by
    rw [MonoidHom.ker_comp_of_injective _ _ e.toLinearEquiv.injective,d.kernel_eq]
  equivariant g w := by
    change e ((d.coordinates _).toAdd) = σ g (e (d.coordinates w).toAdd)
    rw [d.equivariant]
    exact e.isIntertwining g _

/-- Actual marked subgroup sections in the dual-hexacode and tetrad permutation
coordinates. Both literal denominators are unchanged by the coordinate equivalences. -/
theorem marked_factor_sections {G : Type*} [Group G]
    (S : Sextet) (R W U Z : Subgroup G) [IsElementaryAbelian 2 W]
    (hWR : W ≤ R) (hRW : R ≤ normalizer (W : Set G))
    (hUW : U ≤ W) (hZU : Z ≤ U) (hRU : R ≤ normalizer (U : Set G))
    (r : R →* sextetStabilizer S) (F : Additive W ≃ₗ[ZMod 2] Cocode)
    (hF : ∀ (x : R) (w : W),
      F (Additive.ofMul (W.normalizerMonoidHom ⟨x,hRW x.property⟩ w)) =
        cocodeRepresentation (r x).val (F (Additive.ofMul w)))
    (hpair : ∀ w : W, (w : G) ∈ U ↔ F (Additive.ofMul w) ∈ sextetPairSpace S)
    (hline : ∀ w : W, (w : G) ∈ Z ↔ F (Additive.ofMul w) ∈ sextetTetradLine S) :
    Nonempty (BinaryConjugationSection R U Z (middleAction S r)) ∧
    Nonempty (BinaryConjugationSection R W U (topAction S r)) := by
  obtain ⟨⟨dm⟩,⟨dt⟩⟩ := marked_quotient_sections S R W U Z hWR hRW hUW hZU hRU r F hF hpair hline
  exact ⟨⟨section_transport dm (middleEquiv S r)⟩,⟨section_transport dt (topEquiv S r)⟩⟩

end CFSG.Quasithin.Chapter7.NormalizedSource.MathieuSextet
