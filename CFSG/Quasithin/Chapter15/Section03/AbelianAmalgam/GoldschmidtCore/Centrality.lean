module

public import CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GoldschmidtCore.Centrality.CommonCoreIndex
public import Theory.SpecificGroups.OrthogonalFourBinary.NaturalAction
public import Theory.ElementaryAbelian.AbelianNormalClosure

/-!
# Checked reductions for the missing centrality clause

Let `H = G₀` be the published terminal amalgam and `Q = O₂(H)`.
The established containment `V ≤ Q` and Sylow assertion put the actual
span `U = ⟨Vᴴ⟩` inside `Q ≤ T_E`. Source 15.3.46(4) makes every one
of its generating conjugates centralize `V`. Thus `U ≤ C_G(V)`;
since `H` normalizes `U`, it normalizes `C_G(U)`, so `V ≤ C_G(U)`
extends to `U ≤ C_G(U)`. The compatible binary coordinates then give
exponent two. This proves elementary abelianness without 15.3.68(2).

The actual centralizer `C_H(U)` is a normal two-subgroup, hence lies in
`Q`. This is only one direction of the kernel equality needed on p.1155.
Neither abelianness of `U` nor this inclusion proves `Q ≤ C_G(U)`.
For example, a normal four-group in the dihedral group of order eight
has an elementary normal closure and a two-group centralizer but is
not centralized by the whole two-core. That example addresses only
this shortcut, not the full source hypotheses.

Normality of `Q` does prove `⟨Ω₁(Z(T))ᴴ⟩ ≤ Z(Q)`, since `Q ≤ T`.
The corresponding extension from this seed span to all of `V` remains
unproved. `CommonCoreIndex` rules out replacing it by a bound on the
intersection of the two local cores. No completed 15.3.68(2), faithful
`H/Q` action, or adequate replacement for it is asserted here.

Source: Aschbacher–Smith, combined manuscript (1 March 2004),
15.3.46(4), 15.3.67–68 and the terminal module argument,
printed pp.1141 and 1152–1155, PDF pp.1158 and 1169–1172.
-/

public section

open Subgroup Stellmacher
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GoldschmidtCore.Centrality
variable {G : Type*} [Group G]

private theorem normalizes_core (H : Subgroup G) :
    H ≤ normalizer (twoCoreAmbient H : Set G) :=
  H.le_normalizer.trans (normalizer_le_normalizer_characteristic_image H (pCore 2 H))

private theorem normalizes_centralizer {H K : Subgroup G}
    (hHK : H ≤ normalizer (K : Set G)) :
    H ≤ normalizer (centralizer (K : Set G) : Set G) :=
  hHK.trans ((normal_subgroupOf_iff_le_normalizer
    (centralizer_le_normalizer (K : Set G))).mp inferInstance)

/-- Normality puts the terminal core in the selected Sylow subgroup. -/
theorem core_le_lineT (Y T E F : Subgroup G)
    (hT : IsSylowSubgroupIn (lineT T E) (amalgamGroup Y T E F)) :
    twoCoreAmbient (amalgamGroup Y T E F) ≤ lineT T E := by
  obtain ⟨S,hS⟩ := hT
  rw [← hS]
  exact map_mono (pCore_isPGroup.le_sylow_of_normal S)

/-- The actual conjugate span stays inside the terminal core. -/
theorem span_le_core (Y T V E F : Subgroup G)
    (hVQ : V ≤ twoCoreAmbient (amalgamGroup Y T E F)) :
    conjugateSpanBy V (amalgamGroup Y T E F) ≤ twoCoreAmbient (amalgamGroup Y T E F) :=
  conjugateSpanBy_le hVQ (normalizes_core _)

/-- Source 15.3.46(4) proves that the actual span is abelian, without
assuming that the core centralizes it. -/
theorem span_commutative (M Y T V E F : Subgroup G)
    (hTM : T ≤ M)
    (hVQ : V ≤ twoCoreAmbient (amalgamGroup Y T E F))
    (hT : IsSylowSubgroupIn (lineT T E) (amalgamGroup Y T E F))
    (hweak : ∀ g : G, V.map (MulAut.conj g).toMonoidHom ≤ M →
      V.map (MulAut.conj g).toMonoidHom ≤ centralizer (V : Set G)) :
    IsMulCommutative (conjugateSpanBy V (amalgamGroup Y T E F)) := by
  let H := amalgamGroup Y T E F
  let U := conjugateSpanBy V H
  have hUM : U ≤ M := (span_le_core Y T V E F hVQ).trans
    ((core_le_lineT Y T E F hT).trans (inf_le_left.trans hTM))
  have hUCV : U ≤ centralizer (V : Set G) := by
    apply (closure_le _).mpr
    rintro x ⟨g,hg,v,hv,rfl⟩
    apply hweak g ?_ (mem_map_of_mem (MulAut.conj g).toMonoidHom hv)
    rintro x ⟨w,hw,rfl⟩
    exact hUM (subset_closure ⟨g,hg,w,hw,rfl⟩)
  apply le_centralizer_iff_isMulCommutative.mp
  exact conjugateSpanBy_le (le_centralizer_iff.mp hUCV)
    (normalizes_centralizer (le_normalizer_conjugateSpanBy V H))

private theorem natural_pow_two (M V : Subgroup G)
    (d : OrthogonalFourBinary.NaturalAction V M) (v : V) : v ^ 2 = 1 := by
  apply d.coordinates.injective
  rw [map_pow, map_one]
  change Multiplicative.ofAdd (2 • Multiplicative.toAdd (d.coordinates v)) = 1
  have htwo : (2 : OrthogonalFourBinary.Space) = 0 := by decide
  simp [nsmul_eq_mul, htwo]

/-- The genuine natural-action coordinates supply exponent two for the
abelian span. This does not descend the action through the two-core. -/
theorem span_elementary (M Y T V E F : Subgroup G)
    (d : OrthogonalFourBinary.NaturalAction V M)
    (hTM : T ≤ M)
    (hVQ : V ≤ twoCoreAmbient (amalgamGroup Y T E F))
    (hT : IsSylowSubgroupIn (lineT T E) (amalgamGroup Y T E F))
    (hweak : ∀ g : G, V.map (MulAut.conj g).toMonoidHom ≤ M →
      V.map (MulAut.conj g).toMonoidHom ≤ centralizer (V : Set G)) :
    IsElementaryAbelian 2 (conjugateSpanBy V (amalgamGroup Y T E F)) := by
  let : IsMulCommutative (closure {x | ∃ h ∈ amalgamGroup Y T E F,
      ∃ z ∈ V, h * z * h⁻¹ = x}) :=
    span_commutative M Y T V E F hTM hVQ hT hweak
  apply IsElementaryAbelian.closure_of_isMulCommutative
  rintro x ⟨g,_,v,hv,rfl⟩
  have hp : v ^ 2 = 1 := congrArg Subtype.val (natural_pow_two M V d ⟨v,hv⟩)
  rw [conj_pow, hp, mul_one, mul_inv_cancel]

/-- The kernel of the span action is contained in the terminal two-core.
The reverse inclusion is the unresolved centrality obligation. -/
theorem span_centralizer_le_core (Y T V E F : Subgroup G)
    (hC : IsPGroup 2 (centralizer (V : Set G))) :
    amalgamGroup Y T E F ⊓ centralizer (conjugateSpanBy V (amalgamGroup Y T E F) : Set G) ≤
      twoCoreAmbient (amalgamGroup Y T E F) := by
  let H := amalgamGroup Y T E F
  let U := conjugateSpanBy V H
  have hn : ((centralizer (U : Set G)).subgroupOf H).Normal :=
    normal_subgroupOf_of_le_normalizer
      (normalizes_centralizer (le_normalizer_conjugateSpanBy V H))
  have hp : IsPGroup 2 (centralizer (U : Set G)) :=
    hC.to_le (centralizer_le (le_conjugateSpanBy V H))
  have hle : (centralizer (U : Set G)).subgroupOf H ≤ pCore 2 H :=
    le_sSup ⟨hn,hp.comap_subtype⟩
  intro x hx
  exact mem_map.mpr ⟨⟨x,hx.1⟩,hle hx.2,rfl⟩

private theorem central_seed_span_le_center (Y T V E F Z : Subgroup G)
    (hZV : Z ≤ V) (hZC : Z ≤ centralizer (T : Set G))
    (hVQ : V ≤ twoCoreAmbient (amalgamGroup Y T E F))
    (hT : IsSylowSubgroupIn (lineT T E) (amalgamGroup Y T E F)) :
    conjugateSpanBy Z (amalgamGroup Y T E F) ≤
      (center (twoCoreAmbient (amalgamGroup Y T E F))).map
        (twoCoreAmbient (amalgamGroup Y T E F)).subtype := by
  let H := amalgamGroup Y T E F
  let Q := twoCoreAmbient H
  have hQ : H ≤ normalizer (Q : Set G) := normalizes_core H
  have hUQ : conjugateSpanBy Z H ≤ Q := conjugateSpanBy_le (hZV.trans hVQ) hQ
  have hUC : conjugateSpanBy Z H ≤ centralizer (Q : Set G) :=
    conjugateSpanBy_le
      (hZC.trans (centralizer_le ((core_le_lineT Y T E F hT).trans inf_le_left)))
      (normalizes_centralizer hQ)
  intro z hz
  refine mem_map.mpr ⟨⟨z,hUQ hz⟩,?_,rfl⟩
  apply mem_center_iff.mpr
  intro q
  exact Subtype.ext (mem_centralizer_iff.mp (hUC hz) q q.property)

/-- The span of the actual Sylow-center seed is central in the core.
This conclusion concerns the seed span, not the larger span of `V`. -/
theorem sylow_seed_span_le_center (Y V E F : Subgroup G) (T : Sylow 2 G)
    (hZV : centralInvolutions T ≤ V)
    (hVQ : V ≤ twoCoreAmbient (amalgamGroup Y T E F))
    (hT : IsSylowSubgroupIn (lineT T E) (amalgamGroup Y T E F)) :
    conjugateSpanBy (centralInvolutions T) (amalgamGroup Y T E F) ≤
      (center (twoCoreAmbient (amalgamGroup Y T E F))).map
        (twoCoreAmbient (amalgamGroup Y T E F)).subtype := by
  apply central_seed_span_le_center Y T V E F (centralInvolutions T) hZV ?_ hVQ hT
  rintro z ⟨zt,⟨zc,_,rfl⟩,rfl⟩
  apply mem_centralizer_iff.mpr
  intro t ht
  exact congrArg (fun x : T => (x : G)) (mem_center_iff.mp zc.property ⟨t,ht⟩)


end CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GoldschmidtCore.Centrality
