module
public import CFSG.Quasithin.Chapter12.Section03.SourceAlternatingSeven.LocalAnalysisNormalizer
public import Theory.Representation.BinarySevenCode.WeightOrbits
public import Theory.Representation.BinarySevenCode.FixedWeights
public import Theory.GroupTheory.WeakClosureSetFusion

/-!
# Orbits, central representatives, and fusion for the A₇ row

Once the entire chosen V has natural coordinates, its L-orbits are exactly
its weight classes. Every two-subgroup of S₇ fixes a word of each nonzero
even weight, so each orbit meets C_V(T). Burnside fusion in C_G(T), followed
by the TI property of V in N_G(L), proves that L controls ambient fusion
when the earlier Sylow-normalizer bound N_G(T) ≤ N_G(L) is supplied.

The final constructor combines these proofs with explicit natural coordinates
and the two ambient point-centralizer bounds. Those inputs, and the earlier
Sylow-normalizer bound, remain separate source obligations; this module does
not assert that the A₇ case has been excluded.

Source: Aschbacher--Smith, 12.3.4(1--2), 12.3.5, printed pp.808--809;
the Sylow-normalizer bound used there is 3.3.1, printed pp.586--598.
-/

@[expose] public noncomputable section
open Subgroup
namespace CFSG.Quasithin.Chapter12.Section03.SourceAlternatingSeven
open Section02 BinarySevenCode
universe u
variable {G : Type u} [Group G] [Finite G]
variable {T : Sylow 2 G} {L V : Subgroup G} {S : Setup T L V}
namespace Setup.NaturalCoordinates
variable (E : S.NaturalCoordinates)
include E

/-- The actual component orbits are the even-weight classes. -/
theorem component_conjugate_iff_weight_eq (x y : V) :
    (∃ l : L, V.normalizerMonoidHom ⟨l,S.chosen.normalizes l.property⟩ x = y) ↔
      weight (E.coordinates x).toAdd.val = weight (E.coordinates y).toAdd.val := by
  constructor
  · rintro ⟨l,rfl⟩
    rw [E.equivariant]
    exact (weight_evenRepresentation _ _).symm
  · intro hw
    obtain ⟨a,ha⟩ := exists_alternating_of_weight_eq (E.coordinates x).toAdd
      (E.coordinates y).toAdd hw
    obtain ⟨l,hl⟩ := S.projection_surjective a
    refine ⟨l,E.coordinates.injective (Multiplicative.toAdd.injective ?_)⟩
    rw [E.equivariant,hl,ha]

/-- Every normalizer conjugation of a point is realized by the original L. -/
theorem normalizer_fusion
    (structural : Structural1222 KnownSimple.IsKnownSimple.{u})
    (n : normalizer (V : Set G)) (x : V) :
    ∃ l : L, V.normalizerMonoidHom ⟨l,S.chosen.normalizes l.property⟩ x =
      V.normalizerMonoidHom n x := by
  apply (component_conjugate_iff_weight_eq E _ _).mpr
  have he := (E.sourceNormalizerModel structural).equivariant n x
  change (E.coordinates (V.normalizerMonoidHom n x)).toAdd = _ at he
  rw [he]
  exact (weight_evenRepresentation _ _).symm

/-- TI reduces fusion in N(L) to fusion in N(V), hence to L. -/
theorem component_normalizer_fusion
    (structural : Structural1222 KnownSimple.IsKnownSimple.{u})
    {x y m : G} (hx : x ∈ V) (hy : y ∈ V) (hy1 : y ≠ 1)
    (hm : m ∈ normalizer (L : Set G)) (he : m*x*m⁻¹ = y) :
    ∃ l ∈ L, l*x*l⁻¹ = y := by
  have hmV : m ∈ normalizer (V : Set G) := by
    rcases CFSG.Quasithin.Chapter12.Section02.Hypothesis1223.source_chosen_TI
      S.hypothesis structural S.chosen m hm with hd | hn
    · exact False.elim (hy1 (mem_bot.mp (hd ▸
        (show y ∈ V ⊓ V.map (MulAut.conj m).toMonoidHom from
          ⟨hy,⟨x,hx,he⟩⟩))))
    · exact mem_normalizer_iff_map_conj_eq.mpr hn
  obtain ⟨l,hl⟩ := normalizer_fusion E structural ⟨m,hmV⟩ ⟨x,hx⟩
  exact ⟨l,l.property,(congrArg Subtype.val hl).trans he⟩

/-- Each nonzero weight has a representative in the ambient C_G(T). -/
theorem central_representative_weight
    (structural : Structural1222 KnownSimple.IsKnownSimple.{u})
    {n : ℕ} (hn : n = 2 ∨ n = 4 ∨ n = 6) :
    ∃ z : V, weight (E.coordinates z).toAdd.val = n ∧
      (z : G) ∈ centralizer (T : Set G) := by
  let hTV : (T : Subgroup G) ≤ normalizer (V : Set G) :=
    ((structural G T L S.hypothesis).2.2 V S.chosen).1
  let f : T →* Equiv.Perm (Fin 7) :=
    (E.sourceNormalizerModel structural).permutation.comp (inclusion hTV)
  obtain ⟨w,hw,hfix⟩ := exists_fixed_weight T.isPGroup' f hn
  let z : V := E.coordinates.symm (Multiplicative.ofAdd w)
  have hz : (E.coordinates z).toAdd = w := by
    simp only [z,E.coordinates.apply_symm_apply,toAdd_ofAdd]
  refine ⟨z,by rw [hz]; exact hw,?_⟩
  intro t ht
  have he := (E.sourceNormalizerModel structural).equivariant ⟨t,hTV ht⟩ z
  change (E.coordinates (V.normalizerMonoidHom ⟨t,hTV ht⟩ z)).toAdd = _ at he
  change _ = evenRepresentation (f ⟨t,ht⟩) (E.coordinates z).toAdd at he
  rw [hz,hfix] at he
  have he' : V.normalizerMonoidHom ⟨t,hTV ht⟩ z = z :=
    E.coordinates.injective (Multiplicative.toAdd.injective (he.trans hz.symm))
  exact mul_inv_eq_iff_eq_mul.mp (congrArg Subtype.val he')

/-- Each nonidentity point has a component conjugate centralizing the Sylow group. -/
theorem central_representative
    (structural : Structural1222 KnownSimple.IsKnownSimple.{u})
    (x : V) (hx : x ≠ 1) :
    ∃ z : V, (z : G) ∈ centralizer (T : Set G) ∧
      ∃ l : L, V.normalizerMonoidHom ⟨l,S.chosen.normalizes l.property⟩ x = z := by
  have hw : (E.coordinates x).toAdd.val ≠ 0 := by
    intro he
    apply hx
    apply E.coordinates.injective
    apply Multiplicative.toAdd.injective
    rw [map_one]
    exact Subtype.ext he
  obtain ⟨z,hz,hzt⟩ := E.central_representative_weight structural
    (weight_of_mem_evenWords (E.coordinates x).toAdd.property hw)
  refine ⟨z,hzt,(E.component_conjugate_iff_weight_eq x z).mpr hz.symm⟩

/-- The source Burnside--TI argument, with its earlier Sylow-normalizer bound
kept explicit. This controls ambient fusion, not merely N(V)-fusion. -/
theorem controlsFusion
    (structural : Structural1222 KnownSimple.IsKnownSimple.{u})
    (hNT : normalizer (T : Set G) ≤ normalizer (L : Set G))
    (x y : G) (hx : x ∈ V) (hy : y ∈ V) (hx1 : x ≠ 1) (hy1 : y ≠ 1)
    (hxy : ∃ g : G, g*x*g⁻¹ = y) : ∃ l ∈ L, l*x*l⁻¹ = y := by
  have hx1' : (⟨x,hx⟩ : V) ≠ 1 := fun h => hx1 (congrArg Subtype.val h)
  have hy1' : (⟨y,hy⟩ : V) ≠ 1 := fun h => hy1 (congrArg Subtype.val h)
  obtain ⟨z,hzt,l,hl⟩ := E.central_representative structural ⟨x,hx⟩ hx1'
  obtain ⟨w,hwt,k,hk⟩ := E.central_representative structural ⟨y,hy⟩ hy1'
  have hl' : (l:G)*x*(l:G)⁻¹ = z := congrArg Subtype.val hl
  have hk' : (k:G)*y*(k:G)⁻¹ = w := congrArg Subtype.val hk
  have hzw : IsConj (z:G) (w:G) := by
    obtain ⟨g,hg⟩ := hxy
    apply isConj_iff.mpr
    refine ⟨(k:G)*g*(l:G)⁻¹,?_⟩
    rw [← hl',← hk']
    calc
      _ = (k:G)*(g*x*g⁻¹)*(k:G)⁻¹ := by group
      _ = _ := by rw [hg]
  have hweak : ∀ g : G, (T : Subgroup G).map (MulAut.conj g).toMonoidHom ≤
      (T : Subgroup G) → g ∈ normalizer (T : Set G) := by
    intro g hg
    apply mem_normalizer_iff_map_conj_eq.mpr
    exact ((g • T).is_maximal' T.isPGroup' hg).symm
  obtain ⟨n,hn,hne⟩ := T.weakly_closed_normalizer_controls_centralizer_fusion
    (T : Subgroup G) le_rfl hweak hzt hwt hzw
  have hw1 : (w:G) ≠ 1 := by
    intro h
    apply hy1
    have h' := hk'.trans h
    have : (k:G)⁻¹ * ((k:G)*y*(k:G)⁻¹) * (k:G) = (k:G)⁻¹*1*(k:G) :=
      congrArg (fun a : G => (k:G)⁻¹*a*(k:G)) h'
    simpa only [mul_assoc,inv_mul_cancel_left,mul_inv_cancel_left,mul_one,inv_mul_cancel] using this
  obtain ⟨a,ha,he⟩ := E.component_normalizer_fusion structural z.property w.property
    hw1 (hNT hn) hne
  refine ⟨(k:G)⁻¹*a*(l:G),L.mul_mem (L.mul_mem (L.inv_mem k.property) ha) l.property,?_⟩
  calc
    _ = (k:G)⁻¹*(a*((l:G)*x*(l:G)⁻¹)*a⁻¹)*(k:G) := by group
    _ = (k:G)⁻¹*(w:G)*(k:G) := by rw [hl',he]
    _ = y := by rw [← hk']; group

/-- Assembly of 12.3.3--8 once the natural-module, earlier Sylow-normalizer,
and ambient point-centralizer inputs have actually been proved. -/
def localAnalysis
    (structural : Structural1222 KnownSimple.IsKnownSimple.{u})
    (hNT : normalizer (T : Set G) ≤ normalizer (L : Set G))
    (hpoints : ∀ v : V, v ≠ 1 →
      (weight (E.coordinates v).toAdd.val = 2 ∨
       weight (E.coordinates v).toAdd.val = 6) →
      centralizer ({(v:G)} : Set G) ≤ normalizer (L : Set G)) : S.LocalAnalysis where
  model := E.sourceNormalizerModel structural
  component_action := E.sourceNormalizerModel_component structural
  controlsFusion := E.controlsFusion structural hNT
  pointCentralizers := hpoints

end Setup.NaturalCoordinates
end CFSG.Quasithin.Chapter12.Section03.SourceAlternatingSeven
