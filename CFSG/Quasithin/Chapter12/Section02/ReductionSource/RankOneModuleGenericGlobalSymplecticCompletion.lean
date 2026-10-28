module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalSymplecticCompletion
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.RankOneModuleGenericGlobalSymplecticMaximal

/-!
# Genuine symplectic extension data in the original Chapter12 setup

The Chapter6 construction is applied with W = wholeReduced T L. Both
compatible amalgam comparisons allow either orientation, and the whole
residual K = O²(H) is retained. The completion lives in the actual join of
N_G(L) and N_G(K), has their full overlap and faithful coset action, and
inherits the order bound against the full automorphism extension. Its native
Cartan has no nonidentity unipotent fixed element, including at exponent two.

The five-path action and path census are proved for this actual completion.
The full order bound forces smallness, a generalized quadrangle, equality
of full extension orders, and generation of G by the two original normalizers.
The ambient completion retains their actual intersection and either endpoint
orientation. The canonical Cartan apartment and common-cover proof now give
symplectic identification and GlobalExit at the original exponent n > 1.
The genuine compatible extension and ambient bound retain their earlier-source
producer, with final discharge in generic-global.

Source: Aschbacher–Smith F.4.3–6, F.4.10, F.4.16 and F.4.24, printed
pp.274–279,282,287–288, and the original Chapter12 application on p.795
of `refs/quasithin.pdf`.
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter6.Source.RankOneGeneric ChapterF.SourceCompletion.SymplecticFour
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V H : Subgroup G} (D : ChosenModule T L V)
include D

/-- Apply the extension completion construction to W = wholeReduced T L.
Both the pure parabolic comparison and the extension comparison retain either
orientation and their compatible whole-overlap maps. -/
theorem rankOne_global_symplectic_extension_completion
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    {n : ℕ} (hn : 1 < n)
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2^n))
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    {A B : Subgroup G} (d : Global.Preparation T L H A B (residual H))
    (hp : Group.IsPerfect (residual H))
    (F : Type) [Field F] [Finite F] [CharP F 2]
    {m : ℕ} (hm : 0 < m) (hF : Nat.card F = 2^m)
    (he : Nonempty (RankTwoAmalgam.Iso
      (Global.sourceParabolicAmalgam ![L,residual H] (Global.sourceS L H))
      (ChapterF.GreenBook.LieModels.SymplecticFour.amalgam F)) ∨
      Nonempty (RankTwoAmalgam.Iso
      (Global.sourceParabolicAmalgam ![L,residual H] (Global.sourceS L H))
      (ChapterF.GreenBook.LieModels.SymplecticFour.amalgam F).reverse))
    (E : SourceExtension F)
    (hext : Nonempty (RankTwoAmalgam.Iso
      (Global.SymplecticCompletion.diagram L (residual H)) E.amalgam) ∨
      Nonempty (RankTwoAmalgam.Iso
      (Global.SymplecticCompletion.diagram L (residual H)) E.amalgam.reverse))
    (hcard : Nat.card G ≤ Nat.card E.carrier) :
    m = n ∧ Nat.card F = 2^n ∧
      Chapter5.Section03GreenExtension.SourceLocalConditions
        (Global.normalizerAmalgam L (residual H)) L (residual H) ((T : Subgroup G) ⊓ L) ∧
      ∃ c : Completion E (Global.SymplecticCompletion.join L (residual H)),
        c.middle.range = (normalizer (L : Set G) ⊓ normalizer (residual H : Set G)).subgroupOf
          (Global.SymplecticCompletion.join L (residual H)) ∧
        c.left.range ⊓ c.right.range = c.middle.range ∧
        Nat.card (Global.SymplecticCompletion.join L (residual H)) ≤ Nat.card E.carrier ∧
        c.middle.range.normalCore = ⊥ ∧
        Function.Injective (MulAction.toPermHom (Global.SymplecticCompletion.join L (residual H))
          (Subgroup.CosetGeometry.RankTwo.Vertex c.cosetFamily)) ∧
        Nat.card c.unipotentMap.range = Nat.card F ^ 4 ∧
        Nat.card c.torusMap.range = (Nat.card F - 1)^2 ∧
        c.torusMap.range ≤ normalizer (c.unipotentMap.range : Set (Global.SymplecticCompletion.join L (residual H))) ∧
        c.unipotentMap.range ⊓ centralizer
          (c.torusMap.range : Set (Global.SymplecticCompletion.join L (residual H))) = ⊥ :=
  d.symplectic_extension_completion (D.rankOne_generic_input_of_many h hmany hn hpsl)
    hH hp F hm hF he E hext hcard

/-- Apply the proved extension path action and order-forced four-path
collision to the original whole-reduced module, in either marking orientation. -/
theorem rankOne_global_symplectic_extension_paths
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    {n : ℕ} (hn : 1 < n)
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2^n))
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    {A B : Subgroup G} (d : Global.Preparation T L H A B (residual H))
    (hp : Group.IsPerfect (residual H))
    (F : Type) [Field F] [Finite F] [CharP F 2]
    {m : ℕ} (hm : 0 < m) (hF : Nat.card F = 2^m)
    (he : Nonempty (RankTwoAmalgam.Iso
      (Global.sourceParabolicAmalgam ![L,residual H] (Global.sourceS L H))
      (ChapterF.GreenBook.LieModels.SymplecticFour.amalgam F)) ∨
      Nonempty (RankTwoAmalgam.Iso
      (Global.sourceParabolicAmalgam ![L,residual H] (Global.sourceS L H))
      (ChapterF.GreenBook.LieModels.SymplecticFour.amalgam F).reverse))
    (E : SourceExtension F)
    (hext : Nonempty (RankTwoAmalgam.Iso
      (Global.SymplecticCompletion.diagram L (residual H)) E.amalgam) ∨
      Nonempty (RankTwoAmalgam.Iso
      (Global.SymplecticCompletion.diagram L (residual H)) E.amalgam.reverse))
    (hcard : Nat.card G ≤ Nat.card E.carrier) :
    m = n ∧ Nat.card F = 2^n ∧
      Chapter5.Section03GreenExtension.SourceLocalConditions
        (Global.normalizerAmalgam L (residual H)) L (residual H) ((T : Subgroup G) ⊓ L) ∧
      ∃ c : Completion E (Global.SymplecticCompletion.join L (residual H)),
        c.middle.range = (normalizer (L : Set G) ⊓ normalizer (residual H : Set G)).subgroupOf
          (Global.SymplecticCompletion.join L (residual H)) ∧
        c.left.range ⊓ c.right.range = c.middle.range ∧
        Nat.card (Global.SymplecticCompletion.join L (residual H)) ≤ Nat.card E.carrier ∧
        Nat.card (Subgroup.CosetGeometry.RankTwo.Vertex c.cosetFamily) ≤
          2 * (Nat.card F + 1) * (Nat.card F ^ 2 + 1) ∧
        ∀ v : Subgroup.CosetGeometry.RankTwo.Vertex c.cosetFamily,
          SimpleGraph.PathTransitivePolygon.RootPathTransitive
            (Subgroup.CosetGeometry.RankTwo.graph c.cosetFamily)
            (Global.SymplecticCompletion.join L (residual H)) v 5 ∧
          (∀ k : ℕ, Nat.card {p : SimpleGraph.BasedWalk
            (Subgroup.CosetGeometry.RankTwo.graph c.cosetFamily) (k+1) v // p.Nonbacktracking} =
              (Nat.card F + 1) * Nat.card F ^ k) ∧
          ∃ p q : SimpleGraph.BasedWalk (Subgroup.CosetGeometry.RankTwo.graph c.cosetFamily) 4 v,
            p.Nonbacktracking ∧ q.Nonbacktracking ∧ p ≠ q ∧ p.endpoint = q.endpoint :=
  d.symplectic_extension_paths (D.rankOne_generic_input_of_many h hmany hn hpsl)
    hH hp F hm hF he E hext hcard

/-- In the actual whole-reduced Chapter12 setup, the full extension order
bound gives ambient generation, order equality and quadrangle geometry.
Both marking orientations retain the full original normalizer intersection. -/
theorem rankOne_global_symplectic_extension_geometry
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    {n : ℕ} (hn : 1 < n)
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2^n))
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    {A B : Subgroup G} (d : Global.Preparation T L H A B (residual H))
    (hp : Group.IsPerfect (residual H))
    (F : Type) [Field F] [Finite F] [CharP F 2]
    {m : ℕ} (hm : 0 < m) (hF : Nat.card F = 2^m)
    (he : Nonempty (RankTwoAmalgam.Iso
      (Global.sourceParabolicAmalgam ![L,residual H] (Global.sourceS L H))
      (ChapterF.GreenBook.LieModels.SymplecticFour.amalgam F)) ∨
      Nonempty (RankTwoAmalgam.Iso
      (Global.sourceParabolicAmalgam ![L,residual H] (Global.sourceS L H))
      (ChapterF.GreenBook.LieModels.SymplecticFour.amalgam F).reverse))
    (E : SourceExtension F)
    (hext : Nonempty (RankTwoAmalgam.Iso
      (Global.SymplecticCompletion.diagram L (residual H)) E.amalgam) ∨
      Nonempty (RankTwoAmalgam.Iso
      (Global.SymplecticCompletion.diagram L (residual H)) E.amalgam.reverse))
    (hcard : Nat.card G ≤ Nat.card E.carrier) :
    m = n ∧ Nat.card F = 2^n ∧
      Chapter5.Section03GreenExtension.SourceLocalConditions
        (Global.normalizerAmalgam L (residual H)) L (residual H) ((T : Subgroup G) ⊓ L) ∧
      Global.SymplecticCompletion.join L (residual H) = ⊤ ∧ Nat.card G = Nat.card E.carrier ∧
      ∃ c : Completion E G,
        c.middle.range = normalizer (L : Set G) ⊓ normalizer (residual H : Set G) ∧
        c.left.range ⊓ c.right.range = c.middle.range ∧
        ((c.left.range = normalizer (L : Set G) ∧ c.right.range = normalizer (residual H : Set G)) ∨
         (c.left.range = normalizer (residual H : Set G) ∧ c.right.range = normalizer (L : Set G))) ∧
        (∀ v (p : (Subgroup.CosetGeometry.RankTwo.graph c.cosetFamily).Walk v v),
          p.IsCycle → 8 ≤ p.length) ∧
        (∀ v w, (Subgroup.CosetGeometry.RankTwo.graph c.cosetFamily).dist v w ≤ 4) ∧
        (∃ v, ∃ p : (Subgroup.CosetGeometry.RankTwo.graph c.cosetFamily).Walk v v,
          p.IsCycle ∧ p.length = 8) :=
  d.symplectic_extension_geometry (D.rankOne_generic_input_of_many h hmany hn hpsl)
    hH hp F hm hF he E hext hcard
/-- The original whole-reduced preparation recognizes the ambient PSp₄ group
at the original exponent from the genuine extension and its full order bound. -/
theorem rankOne_global_symplectic_extension_recognition
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    {n : ℕ} (hn : 1 < n)
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2^n))
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    {A B : Subgroup G} (d : Global.Preparation T L H A B (residual H))
    (hp : Group.IsPerfect (residual H))
    (F : Type) [Field F] [Finite F] [CharP F 2]
    {m : ℕ} (hm : 0 < m) (hF : Nat.card F = 2^m)
    (he : Nonempty (RankTwoAmalgam.Iso
      (Global.sourceParabolicAmalgam ![L,residual H] (Global.sourceS L H))
      (ChapterF.GreenBook.LieModels.SymplecticFour.amalgam F)) ∨
      Nonempty (RankTwoAmalgam.Iso
      (Global.sourceParabolicAmalgam ![L,residual H] (Global.sourceS L H))
      (ChapterF.GreenBook.LieModels.SymplecticFour.amalgam F).reverse))
    (E : SourceExtension F)
    (hext : Nonempty (RankTwoAmalgam.Iso
      (Global.SymplecticCompletion.diagram L (residual H)) E.amalgam) ∨
      Nonempty (RankTwoAmalgam.Iso
      (Global.SymplecticCompletion.diagram L (residual H)) E.amalgam.reverse))
    (hcard : Nat.card G ≤ Nat.card E.carrier) :
    m=n ∧ Nat.card F=2^n ∧
      Global.SymplecticCompletion.join L (residual H)=⊤ ∧ Nat.card G=Nat.card E.carrier ∧
      ClassicalGroup.IsPSp G 2 (2^n) :=
  d.symplectic_extension_recognition (D.rankOne_generic_input_of_many h hmany hn hpsl)
    hH hp F hm hF he E hext hcard

/-- Close the symplectic recognition row of the original Chapter12 global exit.
The compatible extension and ambient order inputs retain their earlier-source
producer; no completion-recognition, Weyl or geometry input remains. -/
theorem rankOne_globalExit_of_symplectic_extension
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    {n : ℕ} (hn : 1 < n)
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2^n))
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    {A B : Subgroup G} (d : Global.Preparation T L H A B (residual H))
    (hp : Group.IsPerfect (residual H))
    (F : Type) [Field F] [Finite F] [CharP F 2]
    {m : ℕ} (hm : 0 < m) (hF : Nat.card F = 2^m)
    (he : Nonempty (RankTwoAmalgam.Iso
      (Global.sourceParabolicAmalgam ![L,residual H] (Global.sourceS L H))
      (ChapterF.GreenBook.LieModels.SymplecticFour.amalgam F)) ∨
      Nonempty (RankTwoAmalgam.Iso
      (Global.sourceParabolicAmalgam ![L,residual H] (Global.sourceS L H))
      (ChapterF.GreenBook.LieModels.SymplecticFour.amalgam F).reverse))
    (E : SourceExtension F)
    (hext : Nonempty (RankTwoAmalgam.Iso
      (Global.SymplecticCompletion.diagram L (residual H)) E.amalgam) ∨
      Nonempty (RankTwoAmalgam.Iso
      (Global.SymplecticCompletion.diagram L (residual H)) E.amalgam.reverse))
    (hcard : Nat.card G ≤ Nat.card E.carrier) :
    RankOneModule.GlobalExit G := by
  obtain ⟨_,_,_,_,hsp⟩ := D.rankOne_global_symplectic_extension_recognition
    h hmany hn hpsl hH d hp F hm hF he E hext hcard
  exact Or.inl ⟨n,hn,ClassificationModels.IsRankTwoModel.symplectic (by omega) hsp⟩
end CFSG.Quasithin.Chapter12.Section02.ChosenModule
