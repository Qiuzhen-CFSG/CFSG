module

public import CFSG.Quasithin.ChapterJ.Section04To05.FiveHexagon.InvariantFives

/-!
# Constructing the unique opposite five in the original SL₂(5)

Transport the two actual generating fives of the first opposite SL₂(5)
through the source reflection. They remain I-invariant and distinct.
The original B₅ also belongs to that factor, so the two-pentagon bound
identifies it with one transported generator. The other is constructed as
the unique I-invariant five different from B₅, and together they generate
the same actual centralizer factor.

Source: Aschbacher–Smith, paragraph before J.4.8, printed p.443.
-/

public section
noncomputable section
open Subgroup
namespace CFSG.Quasithin.ChapterJ.RuSubgroup.FiveHexagon.MarkedNormalizer
open Centralizers Centralizers.Choices MarkedInverter DiagonalCentralizer
open Tits.ExceptionalParabolics.FullRee
variable {G : Type*} [Group G] [Finite G] {d : LocalSetup G}
  (c : Choices d) (B5 : Sylow 5 d.toTypeRuSetup.H)
  {F : Subgroup G} (e : first ≃* F)

/-- Construct the opposite original five, and prove it is the unique
I-invariant five in the actual SL₂(5) other than B₅. -/
theorem exists_source_opposite_five
    (hz : (e modelZ:G)=c.z)
    (hfive : (zpowers modelRotation).map (F.subtype.comp e.toMonoidHom)=B5Image B5)
    (hfusion : IsConj (sourceU e) c.z) :
    ∃ K B':Subgroup G, B5Image B5≤K ∧ sourceI e≤normalizer (K:Set G) ∧
      K≤centralizer (sourceIz e:Set G) ∧
      Nonempty (K≃*Matrix.SpecialLinearGroup (Fin 2) (ZMod 5)) ∧
      Nat.card B'=5 ∧ B'≠B5Image B5 ∧ sourceI e≤normalizer (B':Set G) ∧
      K=B5Image B5⊔B' ∧
      ∀ C:Subgroup G,C≤K → Nat.card C=5 → sourceI e≤normalizer (C:Set G) →
        C=B5Image B5 ∨ C=B' := by
  obtain ⟨hu,hi⟩ := source_inverter c B5 e hz hfive
  obtain ⟨K,s,hKdef,hsI,hsu,hsz,hBK,hIK,hKC,heK,_,_,_,_⟩ :=
    exists_source_base_opposite c B5 e hz hfive hfusion
  obtain ⟨eK⟩ := heK
  let X := (fixedFive B5 (c.z*sourceU e)).conjBy s
  let Y := (nextFive c B5 (sourceU e)).conjBy s
  have hgen : K=X⊔Y := by
    rw [hKdef]
    exact Subgroup.map_sup _ _ _
  have hXK : X≤K := hgen.symm ▸ le_sup_left
  have hYK : Y≤K := hgen.symm ▸ le_sup_right
  have hX : Nat.card X=5 := by
    change Nat.card ((fixedFive B5 (c.z*sourceU e)).map (MulAut.conj s).toMonoidHom)=5
    rw [card_map_of_injective (MulAut.conj s).injective]
    exact (source_three_fives c B5 (sourceU e) hu hfusion hi).2.1
  have hY : Nat.card Y=5 := by
    change Nat.card ((nextFive c B5 (sourceU e)).map (MulAut.conj s).toMonoidHom)=5
    rw [card_map_of_injective (MulAut.conj s).injective]
    exact (next_five_structure c B5 (sourceU e) hu hfusion hi).1
  have transport_normalizes (D:Subgroup G) (hn:sourceI e≤normalizer (D:Set G)) :
      sourceI e≤normalizer (D.conjBy s:Set G) := by
    have hh := (map_mono (f:=(MulAut.conj s).toMonoidHom) hn).trans
      (D.le_normalizer_map (MulAut.conj s).toMonoidHom)
    have hs : (sourceI e).map (MulAut.conj s).toMonoidHom=sourceI e :=
      mem_normalizer_iff_map_conj_eq.mp hsI
    rwa [hs] at hh
  have hIX : sourceI e≤normalizer (X:Set G) := transport_normalizes _
    (sourceI_normalizes_fixed B5 e hfive _ ((sourceI e).mul_mem
      (source_marks_mem c e hz).1 (source_marks_mem c e hz).2))
  have hIY : sourceI e≤normalizer (Y:Set G) :=
    transport_normalizes _ (sourceI_normalizes_next c B5 e hz hfive)
  have hne : X≠Y := by
    intro hh
    have hcard := Theory.SpecificGroups.SL2.PermutationFiveImage.card_source eK
    rw [hgen,hh,sup_idem,hY] at hcard
    contradiction
  have hb := source_invariant_five_eq_or_eq c B5 e hz hfive K hKC hIK hBK eK X Y
    (B5Image B5) hXK hYK hBK hX hY (B5Image_card d.card_Z B5) hIX hIY
    (sourceI_le_normalizer B5 e hfive) hne
  obtain ⟨B',hB',hne',hIB',hgen'⟩ : ∃ B':Subgroup G,Nat.card B'=5 ∧ B'≠B5Image B5 ∧
      sourceI e≤normalizer (B':Set G) ∧ K=B5Image B5⊔B' := by
    rcases hb with hb|hb
    · exact ⟨Y,hY,fun h => hne (hb.symm.trans h.symm),hIY,by rw [hb];exact hgen⟩
    · exact ⟨X,hX,fun h => hne (h.trans hb),hIX,by rw [hb,sup_comm];exact hgen⟩
  refine ⟨K,B',hBK,hIK,hKC,⟨eK⟩,hB',hne',hIB',hgen',?_⟩
  intro C hCK hC hIC
  exact source_invariant_five_eq_or_eq c B5 e hz hfive K hKC hIK hBK eK
    (B5Image B5) B' C hBK (hgen'.symm ▸ le_sup_right) hCK
    (B5Image_card d.card_Z B5) hB' hC (sourceI_le_normalizer B5 e hfive) hIB' hIC hne'.symm

end CFSG.Quasithin.ChapterJ.RuSubgroup.FiveHexagon.MarkedNormalizer
