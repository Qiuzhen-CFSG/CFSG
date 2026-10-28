module
public import CFSG.Quasithin.ChapterE.Section02.Structure.SymplecticFour.SourceAbsoluteSocle
public import Theory.SpecificGroups.SymplecticFour.TransvectionRecognition.SL2NormalizerQuadratic
public import CFSG.Quasithin.ClassicalModels
public import Theory.SpecificGroups.SL2.CardFourEquiv
/-!
# Excluding binary PSL₂ and A₅ for the original transvection socle

The original source gives the same embedded simple socle, its absolute
irreducibility on the original four-dimensional F-space, and normalization
by the literal opposite pair. A binary PSL₂ identification constructs a
quadratic form with the original symplectic polar form and makes the full
normalizer preserve it. This contradicts the original source's quadratic
exclusion. The native IsPSL row and A₅≃PSL₂(4) are discharged with no
additional source premise.

Source: Aschbacher--Smith G.4.1, printed p.342, and E.2.7, pp.219--220.
-/

public noncomputable section
open Subgroup
namespace CFSG.Quasithin.ChapterE.Structure.SymplecticFour
open Theory.SpecificGroups.SymplecticFour TwoConjugate TransvectionRecognition
open ChapterB InvolutionTypes Theory.GroupTheory
variable {G F:Type*} [Group G] [Finite G] [Field F] [Finite F] [CharP F 2]

theorem source_transvection_socle_not_psl2
    {n:ℕ} (hF:Nat.card F=2^n) (hn:1<n)
    (T:Sylow 2 G) (hP:IsMinimalParabolicOver T ⊤)
    (hJ:minimalParabolicCore T hP=⊥)
    (L:Subgroup G) [L.Normal] [IsSimpleGroup L] (e:Sp F≃*L)
    (hmark:(T:Subgroup G).comap (L.subtype.comp e.toMonoidHom)=unipotent)
    (hgen:L⊔(T:Subgroup G)=⊤)
    (V:Subgroup G) [IsElementaryAbelian 2 V] (hVT:V≤T)
    (hVM:V≤(minimalParabolicMax T hP).pCoreIn 2)
    (hVN:(T:Subgroup G)≤normalizer (V:Set G)) (hr:2<Nat.card V)
    (hex:∃ h∈oppositePair (V.comap (L.subtype.comp e.toMonoidHom)),IsB1 h)
    {K:Type*} [Field K] [Finite K] [CharP K 2] (f:ℕ) (hcard:Nat.card K=2^f) :
    let H := oppositePair (V.comap (L.subtype.comp e.toMonoidHom))
    let C := transvectionClosure H
    let N := (generalizedFitting C).map (H.subtype.comp C.subtype)
    ¬Nonempty (N≃*Theory.PSL2.Group K) := by
  dsimp only
  let H := oppositePair (V.comap (L.subtype.comp e.toMonoidHom))
  let C := transvectionClosure H
  let N := (generalizedFitting C).map (H.subtype.comp C.subtype)
  obtain ⟨_,hi,hN⟩ := source_transvection_simple_socle_image_absolutelyIrreducible
    hF hn T hP hJ L e hmark hgen V hVT hVM hVN hr hex
  rintro ⟨a⟩
  obtain ⟨Q,hQ,hQI⟩ := exists_normalizer_quadratic_of_psl2_subgroup N hi a f hcard
  exact source_geometry_quadratic_exclusion hF hn T hP hJ L e hmark hgen
    V hVT hVM hVN hr Q hQ (fun g hg=>hQI g (hN hg))

theorem source_transvection_socle_not_isPSL
    {n:ℕ} (hF:Nat.card F=2^n) (hn:1<n)
    (T:Sylow 2 G) (hP:IsMinimalParabolicOver T ⊤)
    (hJ:minimalParabolicCore T hP=⊥)
    (L:Subgroup G) [L.Normal] [IsSimpleGroup L] (e:Sp F≃*L)
    (hmark:(T:Subgroup G).comap (L.subtype.comp e.toMonoidHom)=unipotent)
    (hgen:L⊔(T:Subgroup G)=⊤)
    (V:Subgroup G) [IsElementaryAbelian 2 V] (hVT:V≤T)
    (hVM:V≤(minimalParabolicMax T hP).pCoreIn 2)
    (hVN:(T:Subgroup G)≤normalizer (V:Set G)) (hr:2<Nat.card V)
    (hex:∃ h∈oppositePair (V.comap (L.subtype.comp e.toMonoidHom)),IsB1 h)
    (f:ℕ) :
    let H := oppositePair (V.comap (L.subtype.comp e.toMonoidHom))
    let C := transvectionClosure H
    let N := (generalizedFitting C).map (H.subtype.comp C.subtype)
    ¬ClassicalGroup.IsPSL N 2 (2^f) := by
  dsimp only
  rintro ⟨K,_,_,hcard,⟨a⟩⟩
  let := Fintype.ofFinite K
  let : CharP K 2 := charP_of_card_eq_prime_pow (p:=2) (f:=f)
    (by simpa only [Nat.card_eq_fintype_card] using hcard)
  exact source_transvection_socle_not_psl2 hF hn T hP hJ L e hmark hgen V hVT hVM hVN hr hex f hcard ⟨a⟩

theorem source_transvection_socle_not_alternatingFive
    {n:ℕ} (hF:Nat.card F=2^n) (hn:1<n)
    (T:Sylow 2 G) (hP:IsMinimalParabolicOver T ⊤)
    (hJ:minimalParabolicCore T hP=⊥)
    (L:Subgroup G) [L.Normal] [IsSimpleGroup L] (e:Sp F≃*L)
    (hmark:(T:Subgroup G).comap (L.subtype.comp e.toMonoidHom)=unipotent)
    (hgen:L⊔(T:Subgroup G)=⊤)
    (V:Subgroup G) [IsElementaryAbelian 2 V] (hVT:V≤T)
    (hVM:V≤(minimalParabolicMax T hP).pCoreIn 2)
    (hVN:(T:Subgroup G)≤normalizer (V:Set G)) (hr:2<Nat.card V)
    (hex:∃ h∈oppositePair (V.comap (L.subtype.comp e.toMonoidHom)),IsB1 h)
    :
    let H := oppositePair (V.comap (L.subtype.comp e.toMonoidHom))
    let C := transvectionClosure H
    let N := (generalizedFitting C).map (H.subtype.comp C.subtype)
    ¬Nonempty (N≃*alternatingGroup (Fin 5)) := by
  dsimp only
  rintro ⟨a⟩
  obtain ⟨b⟩ := Matrix.ProjectiveSpecialLinearGroup.equiv_alternatingGroup_of_card_four
    (K:=GaloisField 2 2) (by simpa using GaloisField.card 2 2 (by decide))
  exact source_transvection_socle_not_psl2 hF hn T hP hJ L e hmark hgen V hVT hVM hVN hr hex
    2 (GaloisField.card 2 2 (by decide)) ⟨a.trans b.symm⟩

end CFSG.Quasithin.ChapterE.Structure.SymplecticFour
