module
public import CFSG.Quasithin.ChapterJ.Section04To05.FiveHexagon.DiagonalCentralizer.Unique
public import CFSG.Quasithin.ChapterJ.Section04To05.FiveHexagon.SourceBaseOpposite

/-!
# The original J.4 cyclic-four centralizer and conjugate uniqueness

The genuine marked completion constructs the actual opposite SL₂(5) subgroup
at z. Its placements feed the whole-centralizer theorem and the uniqueness of
its conjugate containing B₅. All actors, quotient maps, I and Iz belong to the
original group. No centralizer, complement-conjugacy or graph-automorphism
assumption is used. The separate reflection comparison remains in the source
hexagon assembly.

Source: Aschbacher–Smith, preparation for J.4.8, printed p.443.
-/

public section
noncomputable section
namespace CFSG.Quasithin.ChapterJ.RuSubgroup.FiveHexagon.DiagonalCentralizer
open CFSG.Quasithin.ChapterF.SourceCompletion.BinaryRee
open Tits.ExceptionalParabolics.FullRee
open Subgroup Centralizers Centralizers.Choices MarkedInverter MarkedNormalizer

theorem source_centralizer_and_unique_conjugate
    {D : Type*} [Group D] (q : Completion D)
    {G : Type*} [Group G] [Finite G] {d : LocalSetup G}
    (c : Choices d) (B5 : Sylow 5 d.toTypeRuSetup.H)
    {F : Subgroup G} (e : first ≃* F) (f : D →* G)
    (hleft : ∀ a : first, f (q.left a) = (e a : G))
    (hz : (e modelZ : G) = c.z)
    (hfive : (zpowers modelRotation).map (F.subtype.comp e.toMonoidHom) = B5Image B5) :
    ∃ (K : Subgroup G) (s : G),
      K = (oppositePair c B5 (sourceU e)).conjBy s ∧
      s∈normalizer (sourceI e:Set G) ∧
      B5Image B5≤K ∧ sourceI e≤normalizer (K:Set G) ∧
      K≤centralizer (sourceIz e:Set G) ∧
      Nonempty (K≃*Matrix.SpecialLinearGroup (Fin 2) (ZMod 5)) ∧
      centralizer (sourceIz e:Set G)=sourceI e⊔d.toTypeRuSetup.U⊔K ∧
      (∀ x:G, x∈centralizer (sourceIz e:Set G) ↔
        ∃ i∈sourceI e, ∃ u∈d.toTypeRuSetup.U, ∃ k∈K, i*u*k=x) ∧
      (∀ g:G, g∈centralizer (sourceIz e:Set G) → B5Image B5≤K.conjBy g → K.conjBy g=K) := by
  obtain ⟨K,s,hKs,hsI,_,_,hBK,hIK,hKC,⟨eK⟩,_⟩ :=
    source_base_opposite q c B5 e f hleft hz hfive
  exact ⟨K,s,hKs,hsI,hBK,hIK,hKC,⟨eK⟩,
    centralizer_eq c B5 e hz hfive K hBK hKC eK,
    mem_centralizer_iff_product c B5 e hz hfive K hBK hKC hIK eK,
    conjugate_eq_of_centralizer c B5 e hz hfive K hBK hKC hIK eK⟩

end CFSG.Quasithin.ChapterJ.RuSubgroup.FiveHexagon.DiagonalCentralizer
