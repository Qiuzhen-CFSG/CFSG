module

public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.Generation.LinearRecognition.Centralizers.UnitaryExclusion.SecondCentralizer.TorusCentralizer.Centralization
public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.Generation.LinearRecognition.Centralizers.UnitaryExclusion.SecondCentralizer.AmbientTorus
public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.Generation.LinearRecognition.Centralizers.UnitaryExclusion.SecondCentralizer.TorusCentralizer.IntrinsicCentralizer.Matrix

/-!
# The intrinsic fixed-torus centralizer in both unitary covers

The standard matrix calculation is transported using the actual simultaneous
Sylow–involution conjugators, then through the cover's given isomorphism.
Thus the centralizer of the fixed part of the literal two-point torus is
contained in the join of that torus with the actual root-generated subgroup.
Both SU₃ and PSU₃ are retained, with separate matrix-field and fixed-field
cardinalities. No geometric or centralizer premise is added.

Source: GLS4, Chapter 4, Lemma 3.6(d), used in Chapter 2 before Lemma 13.2.
The ambient identity is assembled by the parent TorusCentralizer module.
-/

open Subgroup Matrix BenderSuzuki.External
namespace BenderSuzuki.ZD.RankOneModelGeometry.UnitaryTorusCentralizer
open BenderSuzuki.MatrixGroups HermitianForm BorelTorus
open UnitaryTorusCentralization
section Transport
variable {G H : Type*} [Group G] [Group H]

private theorem centralizer_le_of_map (e : G ≃* H) (D R : Subgroup G)
    (S T : Subgroup H) (hD : D.map e.toMonoidHom = S) (hR : R.map e.toMonoidHom = T)
    (hc : centralizer (S : Set H) ≤ T ⊔ S) : centralizer (D : Set G) ≤ R ⊔ D := by
  intro x hx
  have hx' : e x ∈ centralizer (S : Set H) := by
    intro y hy
    rw [← hD] at hy
    obtain ⟨z, hz, rfl⟩ := hy
    simpa only [map_mul, MulEquiv.coe_toMonoidHom] using congrArg e (hx z hz)
  have hh := hc hx'
  rw [← hR, ← hD, ← Subgroup.map_sup] at hh
  obtain ⟨y, hy, he⟩ := hh
  exact e.injective he ▸ hy

private theorem pair_le_of_equiv [Finite G] (e : G ≃* H) (P : Sylow 2 G) (t : G)
    (hc : let Q := P.mapSurjective (f := e.toMonoidHom) e.surjective
      centralizer (twoPoint (normalizer (Q : Set H)) (e t) ⊓
        centralizer ({e t} : Set H) : Set H) ≤
          rootGenerated (Q : Subgroup H) (e t) ⊔
            (twoPoint (normalizer (Q : Set H)) (e t) ⊓ centralizer ({e t} : Set H))) :
    centralizer (twoPoint (normalizer (P : Set G)) t ⊓ centralizer ({t} : Set G) : Set G) ≤
      rootGenerated (P : Subgroup G) t ⊔
        (twoPoint (normalizer (P : Set G)) t ⊓ centralizer ({t} : Set G)) := by
  let Q := P.mapSurjective (f := e.toMonoidHom) e.surjective
  apply centralizer_le_of_map e
    (twoPoint (normalizer (P : Set G)) t ⊓ centralizer ({t} : Set G)) _
    (twoPoint (normalizer (Q : Set H)) (e t) ⊓ centralizer ({e t} : Set H)) _
    ?_ (root_map e (P : Subgroup G) t) hc
  rw [fixed_map, twoPoint_map]
  exact congrArg (fun B => twoPoint B (e t) ⊓ centralizer ({e t} : Set H))
    (Subgroup.map_equiv_normalizer_eq (P : Subgroup G) e)
end Transport

variable {E : Type*} [Field E] [Finite E] (J : HermitianForm 3 E)
  (hJ : J.form = !![0,0,1;0,1,0;1,0,0]) {n : ℕ} (hn : 2 ≤ n)
  (hcard : Nat.card E = (2 ^ n) ^ 2)
  (hfixed : Nat.card {x : E // J.conj x = x} = 2 ^ n)

include hcard in
private theorem charTwo_of_card : CharP E 2 := by
  let := Fintype.ofFinite E
  apply charP_of_card_eq_prime_pow (p := 2) (f := n * 2)
  simpa [Nat.card_eq_fintype_card, pow_mul] using hcard

include hn in
private theorem fixed_card_gt_two : 2 < 2 ^ n := by
  have hh : 2 ^ 2 ≤ 2 ^ n := Nat.pow_le_pow_right (n := 2) (by decide) hn
  omega

include hJ hn hcard hfixed in
/-- The upper bound for an arbitrary actual special-unitary pair. -/
public theorem special_pair (P : Sylow 2 J.specialSubgroup) (t : J.specialSubgroup)
    (ht : BenderSuzuki.PFAppendixIII.IsInvolution t)
    (htB : t ∉ normalizer (P : Set J.specialSubgroup)) :
    centralizer (twoPoint (normalizer (P : Set J.specialSubgroup)) t ⊓
      centralizer ({t} : Set _) : Set _) ≤
        rootGenerated (P : Subgroup J.specialSubgroup) t ⊔
          (twoPoint (normalizer (P : Set J.specialSubgroup)) t ⊓ centralizer ({t} : Set _)) := by
  let : CharP E 2 := charTwo_of_card hcard
  obtain ⟨g, hP, ht', hD⟩ := PairNormalization.special_pair J hJ hn hcard hfixed P t ht htB
  let c := MulAut.conj g
  apply centralizer_le_of_map c
    (twoPoint (normalizer (P : Set J.specialSubgroup)) t ⊓ centralizer ({t} : Set _))
    (rootGenerated (P : Subgroup J.specialSubgroup) t)
    (specialTorus J hJ ⊓ centralizer ({hermitianWeylSU J hJ} : Set _))
    (rootGenerated (specialRoot J hJ) (hermitianWeylSU J hJ)) ?_ ?_
    (special_standard_le J hJ hcard hfixed (fixed_card_gt_two hn))
  · rw [fixed_map, hD, ht']
  · rw [root_map, hP, ht']

include hJ hn hcard hfixed in
/-- The upper bound for an arbitrary actual projective-unitary pair. -/
public theorem projective_pair (P : Sylow 2 (ProjectiveSpecialUnitaryMatrixGroup J))
    (t : ProjectiveSpecialUnitaryMatrixGroup J) (ht : BenderSuzuki.PFAppendixIII.IsInvolution t)
    (htB : t ∉ normalizer (P : Set (ProjectiveSpecialUnitaryMatrixGroup J))) :
    centralizer (twoPoint (normalizer (P : Set (ProjectiveSpecialUnitaryMatrixGroup J))) t ⊓
      centralizer ({t} : Set _) : Set _) ≤
        rootGenerated (P : Subgroup (ProjectiveSpecialUnitaryMatrixGroup J)) t ⊔
          (twoPoint (normalizer (P : Set (ProjectiveSpecialUnitaryMatrixGroup J))) t ⊓
            centralizer ({t} : Set _)) := by
  let : CharP E 2 := charTwo_of_card hcard
  obtain ⟨g, hP, ht', hD⟩ := PairNormalization.projective_pair J hJ hn hcard hfixed P t ht htB
  let c := MulAut.conj g
  apply centralizer_le_of_map c
    (twoPoint (normalizer (P : Set (ProjectiveSpecialUnitaryMatrixGroup J))) t ⊓
      centralizer ({t} : Set _))
    (rootGenerated (P : Subgroup (ProjectiveSpecialUnitaryMatrixGroup J)) t)
    (projectiveTorus J hJ ⊓ centralizer ({hermitianWeylPSU J hJ} : Set _))
    (rootGenerated (projectiveRoot J hJ) (hermitianWeylPSU J hJ)) ?_ ?_
    (projective_standard_le J hJ hcard hfixed (fixed_card_gt_two hn))
  · rw [fixed_map, hD, ht']
  · rw [root_map, hP, ht']

variable {G : Type*} [Group G] [Finite G]

include hJ hn hcard hfixed in
/-- Transport of the intrinsic bound through a genuine special-unitary model. -/
public theorem special_of_equiv (e : G ≃* J.specialSubgroup) (P : Sylow 2 G)
    (t : G) (ht : BenderSuzuki.PFAppendixIII.IsInvolution t) (htB : t ∉ normalizer (P : Set G)) :
    centralizer (twoPoint (normalizer (P : Set G)) t ⊓ centralizer ({t} : Set G) : Set G) ≤
      rootGenerated (P : Subgroup G) t ⊔
        (twoPoint (normalizer (P : Set G)) t ⊓ centralizer ({t} : Set G)) := by
  apply pair_le_of_equiv e P t
  apply special_pair J hJ hn hcard hfixed
  · exact BenderSuzuki.IsInvolution.map_of_injective ht e.toMonoidHom e.injective
  · intro hh
    change e t ∈ normalizer ((P : Subgroup G).map e.toMonoidHom : Set _) at hh
    rw [← Subgroup.map_equiv_normalizer_eq] at hh
    obtain ⟨x, hx, he⟩ := hh
    exact htB (e.injective he ▸ hx)

include hJ hn hcard hfixed in
/-- Transport of the intrinsic bound through the literal projective quotient model. -/
public theorem projective_of_equiv (e : G ≃* ProjectiveSpecialUnitaryMatrixGroup J)
    (P : Sylow 2 G) (t : G) (ht : BenderSuzuki.PFAppendixIII.IsInvolution t)
    (htB : t ∉ normalizer (P : Set G)) :
    centralizer (twoPoint (normalizer (P : Set G)) t ⊓ centralizer ({t} : Set G) : Set G) ≤
      rootGenerated (P : Subgroup G) t ⊔
        (twoPoint (normalizer (P : Set G)) t ⊓ centralizer ({t} : Set G)) := by
  apply pair_le_of_equiv e P t
  apply projective_pair J hJ hn hcard hfixed
  · exact BenderSuzuki.IsInvolution.map_of_injective ht e.toMonoidHom e.injective
  · intro hh
    change e t ∈ normalizer ((P : Subgroup G).map e.toMonoidHom : Set _) at hh
    rw [← Subgroup.map_equiv_normalizer_eq] at hh
    obtain ⟨x, hx, he⟩ := hh
    exact htB (e.injective he ▸ hx)

end BenderSuzuki.ZD.RankOneModelGeometry.UnitaryTorusCentralizer

namespace BenderSuzuki.ZD.UnitaryExclusion
open RankOneModelGeometry

/-- The intrinsic upper bound of GLS4, Chapter 4, Lemma 3.6(d), for either
actual unitary cover and the literal fixed part of the two-point torus. -/
public theorem unitaryCover_fixed_torus_centralizer_le
    {H : Type*} [Group H] [Finite H] {n : ℕ} (hn : 2 ≤ n)
    (hc : IsUnitaryCentralizerCoverAt n H) (P : Sylow 2 H) (s : H)
    (hs : PFAppendixIII.IsInvolution s) (hsN : s ∉ normalizer (P : Set H)) :
    let D := twoPoint (normalizer (P : Set H)) s
    let B := D ⊓ centralizer ({s} : Set H)
    centralizer (B : Set H) ≤ rootGenerated (P : Subgroup H) s ⊔ B := by
  obtain ⟨E, _, _, J, hJ, hcard, hfixed, he | he⟩ := hc
  · obtain ⟨e⟩ := he
    exact UnitaryTorusCentralizer.projective_of_equiv J hJ hn hcard hfixed e P s hs hsN
  · obtain ⟨e⟩ := he
    exact UnitaryTorusCentralizer.special_of_equiv J hJ hn hcard hfixed e P s hs hsN

end BenderSuzuki.ZD.UnitaryExclusion
