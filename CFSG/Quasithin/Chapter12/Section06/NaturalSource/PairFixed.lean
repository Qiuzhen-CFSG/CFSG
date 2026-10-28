module
public import CFSG.Quasithin.Chapter12.Section06.NaturalSource.PairOrthogonal
public import CFSG.Quasithin.Chapter12.Section06.Nonabelian.PairFixed

/-!
# The original pair's singular rank-four generators

The pair geometry supplies an eight-dimensional central quotient and two
singular four-dimensional seed images. The original F.9 separation fixes
each generator's kernel; binary rank-nullity identifies its displacement
with the same seed. This applies to every element outside V5 and its
specified conjugate, including the generators of the already constructed
faithful action of the literal pair image in H/O2(H).

The endpoint discharges extraspeciality and retains the existing plus-type
model, action kernel and quotient compatibility. Earlier point, fixed-space,
intersection and nonsingular-centralizer inputs remain explicit. The
D6/D10/D12 recognition and 12.6.26 abelian-span argument remain open.
Source: Aschbacher--Smith F.9.5(6.ii), pp.319--320, and 12.6.26, p.831.
-/

@[expose] public section
namespace CFSG.Quasithin.Chapter12.Section06.Nonabelian
open Subgroup Theory.GroupTheory
variable {G : Type*} [Group G]

/-- The two original outside generators have exactly their own seed images
as fixed and displacement spaces, of dimension four. The action is the
literal conjugation action on the seed's central quotient. -/
def SquarePairSeedSpaces (V W : Subgroup G) (g : G)
    (hs : IsExtraspecial 2 (W ⊔ W.map (MulAut.conj g).toMonoidHom : Subgroup G)) : Prop :=
  let I := V ⊔ V.map (MulAut.conj g).toMonoidHom
  let P := W ⊔ W.map (MulAut.conj g).toMonoidHom
  letI := hs
  ∀ (n : I ≤ normalizer (P : Set G)) (v : V), v.val ∉ W →
    let α := (ExtraspecialSquare.isometryAction P).comp (seedConjugation I P n)
    let a := α ⟨v.val,mem_sup_left v.property⟩
    let b := α ⟨(MulAut.conj g) v.val,
      mem_sup_right (mem_map_of_mem (MulAut.conj g).toMonoidHom v.property)⟩
    LinearMap.ker (a.val.toLinearMap - LinearMap.id) = ExtraspecialSquare.imageSpace P (W.subgroupOf P) ∧
    LinearMap.range (a.val.toLinearMap - LinearMap.id) = ExtraspecialSquare.imageSpace P (W.subgroupOf P) ∧
    Module.finrank (ZMod 2) (LinearMap.range (a.val.toLinearMap - LinearMap.id)) = 4 ∧
    LinearMap.ker (b.val.toLinearMap - LinearMap.id) =
      ExtraspecialSquare.imageSpace P ((W.map (MulAut.conj g).toMonoidHom).subgroupOf P) ∧
    LinearMap.range (b.val.toLinearMap - LinearMap.id) =
      ExtraspecialSquare.imageSpace P ((W.map (MulAut.conj g).toMonoidHom).subgroupOf P) ∧
    Module.finrank (ZMod 2) (LinearMap.range (b.val.toLinearMap - LinearMap.id)) = 4
end CFSG.Quasithin.Chapter12.Section06.Nonabelian

public section
namespace CFSG.Quasithin.Chapter12.Section06
open Subgroup Theory.GroupTheory
open ChapterF.Section09.Setup.Hypothesis
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V : Subgroup G} [IsElementaryAbelian 2 V]
  (S : SourceHypothesis KnownSimple.IsKnownSimple T L V)
  (D : OrthogonalMarking L V S.chosen.normalizes) (hZ : ZV L V = ⊥) (z : V)

/-- Original fixed and displacement spaces of every outside seed generator.
Extraspeciality is supplied by the original pair geometry in the endpoint below. -/
theorem SourceHypothesis.original_non_two_pair_seed_spaces
    (hz : z ≠ 1)
    (hTV : (T : Subgroup G) ≤ normalizer (V : Set G))
    (hTz : (T : Subgroup G) ≤ normalizer ((D.fullSetup hZ T z).V₁ : Set G))
    (hbound : ∀ g : G, g ∉ normalizer (V : Set G) →
      Nat.card (V ⊓ V.map (MulAut.conj g).toMonoidHom : Subgroup G) ≤ 2 ^ 3)
    (hns : ∀ w : V, D.Nonsingular w → Gv w.val ≤ M L)
    {H : Subgroup G} (hH : H ∈ (D.fullSetup hZ T z).Hz)
    (g : G) (hg : g ∈ H)
    (hn : ¬ IsPGroup 2 (V ⊔ V.map (MulAut.conj g).toMonoidHom : Subgroup G))
    (hs : IsExtraspecial 2 ((D.fullSetup hZ T z).pairSeed g)) :
    Nonabelian.SquarePairSeedSpaces V (D.fullSetup hZ T z).V₅ g hs := by
  let E := D.fullSetup hZ T z
  let I := V ⊔ V.map (MulAut.conj g).toMonoidHom
  let P := E.pairSeed g
  let : IsExtraspecial 2 P := hs
  obtain ⟨_,_,_,hd,hA,_,hB,_,_⟩ := S.original_non_two_pair_plus D hZ z hz hTV hTz hbound hns hH g hg hn
  obtain ⟨hc,_,_,_,_⟩ := S.original_non_two_pair_geometry D hZ z hz hTV hTz hbound hns hH g hg hn
  have h := S.original_f9_of_earlier_geometry D hZ z hz hTV hTz hbound hH
  have hout : ¬ E.Gz ≤ M L := fun hh => hH.2.2 (hH.2.1.trans hh)
  have hp : ∀ t ∈ H, E.V₁ < V ⊓ V.map (MulAut.conj t).toMonoidHom →
      IsPGroup 2 (V ⊔ V.map (MulAut.conj t).toMonoidHom : Subgroup G) :=
    fun t _ => S.original_intersecting_pair_isTwoGroup D hZ z hz hTV hTz hbound hout hns t
  unfold Nonabelian.SquarePairSeedSpaces
  dsimp only
  intro n v hvw
  let x : I := ⟨v.val,mem_sup_left v.property⟩
  let y : I := ⟨(MulAut.conj g) v.val,
    mem_sup_right (mem_map_of_mem (MulAut.conj g).toMonoidHom v.property)⟩
  have hx2 : x^2=1 := Subtype.ext (elemPow_eq_one_of_isElementaryAbelian v.val v.property)
  have hy2 : y^2=1 := by
    apply Subtype.ext
    change ((MulAut.conj g) v.val)^2=1
    rw [←map_pow,elemPow_eq_one_of_isElementaryAbelian v.val v.property,map_one]
  obtain ⟨hka,hkb⟩ := Nonabelian.pair_square_fixed_spaces h (E.perpendicular_index hz)
    hp g hg hn hs hc n v hvw
  have hra := ExtraspecialSquare.range_eq_imageSpace_of_half_fixed
    (seedConjugation I P n x) (by rw [←map_pow,hx2,map_one]) (E.V₅.subgroupOf P) 4 hd hA hka
  have hrb := ExtraspecialSquare.range_eq_imageSpace_of_half_fixed
    (seedConjugation I P n y) (by rw [←map_pow,hy2,map_one])
    ((E.V₅.map (MulAut.conj g).toMonoidHom).subgroupOf P) 4 hd hB hkb
  have hfa := (congrArg (fun K : Submodule (ZMod 2) (ExtraspecialSquare.Space P) =>
    Module.finrank (ZMod 2) K) hra).trans hA
  have hfb := (congrArg (fun K : Submodule (ZMod 2) (ExtraspecialSquare.Space P) =>
    Module.finrank (ZMod 2) K) hrb).trans hB
  exact ⟨hka,hra,hfa,hkb,hrb,hfb⟩

/-- The original faithful orthogonal pair, now with its rank-four fixed and
moved spaces. In particular the generators retained in `SquarePairAction`
have these spaces for the very same element and its specified conjugate. -/
theorem SourceHypothesis.original_non_two_pair_marked_orthogonal
    (hz : z ≠ 1)
    (hTV : (T : Subgroup G) ≤ normalizer (V : Set G))
    (hTz : (T : Subgroup G) ≤ normalizer ((D.fullSetup hZ T z).V₁ : Set G))
    (hbound : ∀ g : G, g ∉ normalizer (V : Set G) →
      Nat.card (V ⊓ V.map (MulAut.conj g).toMonoidHom : Subgroup G) ≤ 2 ^ 3)
    (hns : ∀ w : V, D.Nonsingular w → Gv w.val ≤ M L)
    {H : Subgroup G} (hH : H ∈ (D.fullSetup hZ T z).Hz)
    (g : G) (hg : g ∈ H)
    (hn : ¬ IsPGroup 2 (V ⊔ V.map (MulAut.conj g).toMonoidHom : Subgroup G)) :
    let E := D.fullSetup hZ T z
    Nonempty (E.pairSeed g ≃* DihedralCentralProductFourSix.FourModel) ∧
      ∃ hs : IsExtraspecial 2 (E.pairSeed g),
        Nonabelian.SquarePairAction H V E.V₅ g hs ∧
        Nonabelian.SquarePairSeedSpaces V E.V₅ g hs := by
  obtain ⟨hm,hs,ha⟩ := S.original_non_two_pair_orthogonal D hZ z hz hTV hTz hbound hns hH g hg hn
  exact ⟨hm,hs,ha,S.original_non_two_pair_seed_spaces D hZ z hz hTV hTz hbound hns hH g hg hn hs⟩

end CFSG.Quasithin.Chapter12.Section06
