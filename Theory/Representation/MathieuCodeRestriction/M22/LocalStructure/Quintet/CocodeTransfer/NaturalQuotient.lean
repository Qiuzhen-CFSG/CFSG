module

public import Theory.Representation.MathieuCodeRestriction.M22.LocalStructure.Quintet.CocodeTransfer.NaturalQuotient.Geometry
public import Theory.Representation.MathieuCodeRestriction.M22.LocalStructure.Quintet.CocodeTransfer.NaturalQuotient.Restriction
public import Theory.Representation.MathieuCodeRestriction.M22.LocalStructure.Quintet.CocodeTransfer.NaturalQuotient.CubicFixed
public import Theory.Representation.MathieuCodeRestriction.M22.LocalStructure.Quintet.CocodeTransfer.NaturalQuotient.CubicExactness
public import Theory.Representation.BinaryOffender.EquivariantOffender
public import Theory.Representation.BinaryPermutationMulAction

/-!
# The natural top quotient of the outer M22 quintet

The canonical third-isomorphism equivalence identifies `M22Cocode / V6` with
`Cocode / U7`. Native tetrad parity identifies the latter with the natural
module on the six actual sextet parts. Since Q fixes the part containing the
distinguished pair, deleting that coordinate gives the natural module on the
other five parts. Every map intertwines the literal action.

The only group inputs to surjectivity, the relative kernel identification, and
irreducibility are the earlier H.14 identification of the restricted part-action
kernel with O2(Q), and an isomorphism Q/O2(Q) with S5. No M22 quotient marking,
chief factor, or irreducibility is assumed. These earlier group inputs are
still for the source assembly owner to discharge.

An order-three element has two fixed dimensions in this geometric top model.
Coprime averaging proves compatibility with the source's four fixed dimensions
in the ten-dimensional cocode: the actual middle term also has two. This
argument uses no transvection-factor or middle-module marking premise.

Source: Aschbacher--Smith, combined manuscript of 1 March 2004, H.15.4,
printed p.400, using H.14 and the native top factor of H.15.3.
-/

@[expose] public section

namespace MathieuCode.M22Quintet.CocodeTransfer.NaturalQuotient
open Representation.BinaryOffender
noncomputable section

/-- The native top section, still in the six-part ambient model. -/
def sextetMarking : (M22Cocode ⧸ V6) ≃ₗ[ZMod 2]
    BinaryPermutation.natural (SextetPart m22SourceSextet) :=
  topQuotientEquiv.trans (sextetTopEquiv m22SourceSextet)

lemma sextetMarking_equivariant (g : Q) (v : M22Cocode ⧸ V6) :
    sextetMarking (V6Subrepresentation.quotientRepresentation g v) =
      BinaryPermutation.naturalRepresentation (SextetPart m22SourceSextet)
        (partAction g) (sextetMarking v) := by
  change sextetTopEquiv m22SourceSextet
    (topQuotientEquiv (V6Subrepresentation.quotientRepresentation g v)) =
    BinaryPermutation.naturalRepresentation _ (partAction g)
      (sextetTopEquiv m22SourceSextet (topQuotientEquiv v))
  rw [topQuotientEquiv_equivariant]
  generalize topQuotientEquiv v = w
  induction w using Submodule.Quotient.induction_on with
  | _ w => exact sextetCocodeParity_equivariant m22SourceSextet (QToSextet g) w

/-- Actual parity and coordinate restriction, not a choice of a four-dimensional basis. -/
def marking : (M22Cocode ⧸ V6) ≃ₗ[ZMod 2] BinaryPermutation.natural (Fin 5) :=
  sextetMarking.trans (BinaryPermutation.PointedSix.naturalEquiv partNumbering)

lemma marking_equivariant (g : Q) (v : M22Cocode ⧸ V6) :
    marking (V6Subrepresentation.quotientRepresentation g v) =
      BinaryPermutation.naturalRepresentation (Fin 5) (q g) (marking v) := by
  change BinaryPermutation.PointedSix.naturalEquiv partNumbering
    (sextetMarking (V6Subrepresentation.quotientRepresentation g v)) = _
  rw [sextetMarking_equivariant]
  exact BinaryPermutation.PointedSix.naturalEquiv_equivariant partNumbering
    (partAction g) (q g) (q_part_compatible g) _

def representationEquiv : Representation.Equiv V6Subrepresentation.quotientRepresentation
    ((BinaryPermutation.naturalRepresentation (Fin 5)).comp q) :=
  .mk marking (fun g => by apply LinearMap.ext; intro v; exact marking_equivariant g v)

lemma top_isIrreducible_of_surjective (hsurj : Function.Surjective q) :
    Representation.IsIrreducible V6Subrepresentation.quotientRepresentation := by
  let := BinaryPermutation.alternatingNatural_isIrreducible (Ω := Fin 5) (by decide)
  let : Nontrivial (BinaryPermutation.natural (Fin 5)) :=
    Subrepresentation.irreducible_module_nontrivial
      (BinaryPermutation.alternatingNaturalRepresentation (Ω := Fin 5))
  let : Nontrivial (M22Cocode ⧸ V6Subrepresentation.toSubmodule) :=
    (Equiv.nontrivial_congr marking.toEquiv).mpr inferInstance
  refine { exists_pair_ne := ⟨⊥, ⊤, ?_⟩, eq_bot_or_eq_top := ?_ }
  · intro h
    exact bot_ne_top (congrArg Subrepresentation.toSubmodule h)
  intro P
  let W : Subrepresentation (BinaryPermutation.alternatingNaturalRepresentation (Ω := Fin 5)) :=
    { toSubmodule := P.toSubmodule.map marking.toLinearMap
      apply_mem_toSubmodule := by
        intro g v hv
        obtain ⟨w,hw,rfl⟩ := hv
        obtain ⟨s,hs⟩ := hsurj g.val
        refine ⟨V6Subrepresentation.quotientRepresentation s w,
          P.apply_mem_toSubmodule s hw, ?_⟩
        exact (marking_equivariant s w).trans (by rw [hs]; rfl) }
  rcases eq_bot_or_eq_top W with h | h
  · left
    apply Subrepresentation.toSubmodule_injective
    apply bot_unique
    intro v hv
    have hm : marking v ∈ W := ⟨v,hv,rfl⟩
    rw [h] at hm
    change marking v = 0 at hm
    exact marking.injective (hm.trans marking.map_zero.symm)
  · right
    apply Subrepresentation.toSubmodule_injective
    apply top_unique
    intro v _
    have hm : marking v ∈ W := by rw [h]; trivial
    obtain ⟨w,hw,he⟩ := hm
    exact marking.injective he ▸ hw

lemma top_isIrreducible (hpart : partAction.ker = pCore 2 Q)
    (e : (Q ⧸ pCore 2 Q) ≃* Equiv.Perm (Fin 5)) :
    Representation.IsIrreducible V6Subrepresentation.quotientRepresentation :=
  top_isIrreducible_of_surjective (q_surjective hpart e)

lemma order_three_image (hpart : partAction.ker = pCore 2 Q)
    (g : Q) (hg : orderOf g = 3) : orderOf (q g) = 3 := by
  have hd : orderOf (q g) ∣ 3 := hg ▸ orderOf_map_dvd q g
  rcases (Nat.prime_three.eq_one_or_self_of_dvd _ hd) with h | h
  · have hq : q g = 1 := orderOf_eq_one_iff.mp h
    have hk : g ∈ pCore 2 Q := by
      have hmem : g ∈ q.ker := hq
      rwa [q_ker_eq_partAction_ker, hpart] at hmem
    have hne : (⟨g,hk⟩ : pCore 2 Q) ≠ 1 := by
      intro hh
      have hg1 : g = 1 := congrArg Subtype.val hh
      simp [hg1] at hg
    have ht := (pCore_isPGroup (p := 2) (G := Q)).dvd_orderOf hne
    rw [Subgroup.orderOf_mk, hg] at ht
    norm_num at ht
  · exact h

lemma top_cubic_fixed_finrank (hpart : partAction.ker = pCore 2 Q)
    (g : Q) (hg : orderOf g = 3) :
    Module.finrank (ZMod 2) (fixedSpace V6Subrepresentation.quotientRepresentation
      (Subgroup.zpowers g)) = 2 := by
  have h := marking.finrank_map_eq
    (fixedSpace V6Subrepresentation.quotientRepresentation (Subgroup.zpowers g))
  have hm : (fixedSpace V6Subrepresentation.quotientRepresentation
      (Subgroup.zpowers g)).map marking.toLinearMap =
      fixedSpace (BinaryPermutation.naturalRepresentation (Fin 5))
        (Subgroup.zpowers (q g)) := by
    exact (fixedSpace_map_equivariant V6Subrepresentation.quotientRepresentation
      (BinaryPermutation.naturalRepresentation (Fin 5)) q marking marking_equivariant
      (Subgroup.zpowers g)).trans (congrArg _ (MonoidHom.map_zpowers q g))
  exact h.symm.trans ((congrArg
    (fun W : Submodule (ZMod 2) (BinaryPermutation.natural (Fin 5)) =>
      Module.finrank (ZMod 2) W) hm).trans
    (BinaryPermutation.PointedSix.natural_fixed_finrank_of_order_three
      (q g) (order_three_image hpart g hg)))

/-- Compatibility with the source datum: four fixed dimensions in V give
exactly two in V6 and two in the top. No M22 middle-factor premise is used. -/
lemma source_cubic_fixed_dimensions (hpart : partAction.ker = pCore 2 Q)
    (g : Q) (hg : orderOf g = 3)
    (hfour : Module.finrank (ZMod 2)
      (fixedSpace m22OuterCocodeRepresentation (Subgroup.zpowers g.val)) = 4) :
    Module.finrank (ZMod 2) (fixedSpace V6Subrepresentation.toRepresentation
      (Subgroup.zpowers g)) = 2 ∧
    Module.finrank (ZMod 2) (fixedSpace V6Subrepresentation.quotientRepresentation
      (Subgroup.zpowers g)) = 2 := by
  have ht := top_cubic_fixed_finrank hpart g hg
  have ha := BinaryPermutation.PointedSix.cubic_fixed_finrank_add
    (m22OuterCocodeRepresentation.comp Q.subtype) V6Subrepresentation g
    (hg ▸ pow_orderOf_eq_one g)
  rw [fixedSpace_comp_map, MonoidHom.map_zpowers] at ha
  change Module.finrank (ZMod 2) (fixedSpace V6Subrepresentation.toRepresentation
      (Subgroup.zpowers g)) + Module.finrank (ZMod 2)
      (fixedSpace V6Subrepresentation.quotientRepresentation (Subgroup.zpowers g)) =
      Module.finrank (ZMod 2)
      (fixedSpace m22OuterCocodeRepresentation (Subgroup.zpowers g.val)) at ha
  exact ⟨by omega, ht⟩
end
end MathieuCode.M22Quintet.CocodeTransfer.NaturalQuotient
