module
public import CFSG.Quasithin.Chapter13.Section02.A5Outside.OriginalCentralization.OriginalSelectedCoreSylow

/-!
# The literal selected source clauses put the pair core in S

The actual pair core lies in T. The original right Cartan B normalizes
L, the selected factor R and S, hence its generated core U. Every element
of the original intersection J=N(L)∩H factors as t b with t in T and
b in B. Therefore every J-conjugate of U lies in T, and its whole
J-conjugate span is a normal two-subgroup of J. It lies in O₂(J)=S.

This form consumes the original selected factor's literal source clauses,
including those supplied for the exchanged component. No canonical family
or extra invariance premise is required.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter13.Section02.A5Outside.OriginalCentralization
open Section05.A5Source Chapter6.Source.RankOneGeneric
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V V₁ V₂ V₃ H R A B : Subgroup G}

/-- Literal selection and compatible right Cartan data put the whole
generated pair core in the original source core S. -/
theorem original_selected_pair_core_le_sourceS_of_cartan
    (d : Context T L V V₁ V₂ V₃)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (c : CartanPair T L H A B)
    (hgen : R ⊔ (T : Subgroup G) = H)
    (hind : ((T : Subgroup G) ⊓ normalizer (R : Set G)).relIndex (T : Subgroup G) ≤ 2)
    (hSR : Global.sourceS L H ≤ normalizer (R : Set G))
    (hBR : B ≤ normalizer (R : Set G)) :
    (ChapterF.Source.generated ![L,R] (Global.sourceS L H)).pCoreIn 2 ≤ Global.sourceS L H := by
  let J := Global.intersection L H
  let S := Global.sourceS L H
  let N := ChapterF.Source.generated ![L,R] S
  let U := N.pCoreIn 2
  have hUT : U ≤ (T : Subgroup G) :=
    (original_selected_pair_core_le_normalizing_sylow d hH hgen hind hSR).trans inf_le_left
  have hBS : B ≤ normalizer (S : Set G) :=
    c.right_le.trans (Global.intersection_normalizes_sourceS L H)
  have hBN : B ≤ normalizer (N : Set G) := by
    change B ≤ normalizer ((L ⊔ R ⊔ S : Subgroup G) : Set G)
    apply le_trans _ (normalizer_inf_normalizer_le_normalizer_sup _ _)
    refine le_inf ?_ hBS
    exact (le_inf (c.right_le.trans inf_le_left) hBR).trans
      (normalizer_inf_normalizer_le_normalizer_sup _ _)
  have hBU : B ≤ normalizer (U : Set G) :=
    hBN.trans (normalizer_le_normalizer_characteristic_image N (pCore 2 N))
  let W := conjugateSpanBy U J
  have hWT : W ≤ (T : Subgroup G) := by
    apply (closure_le _).mpr
    rintro x ⟨g,hg,z,hz,rfl⟩
    change g * z * g⁻¹ ∈ (T : Subgroup G)
    obtain ⟨⟨t,b⟩,htb⟩ := (c.sylow_complement d.normalizes_L hH.1.1.2).2 ⟨g,hg⟩
    have ht : (t.val : G) ∈ (T : Subgroup G) := t.property
    have hb : (b.val : G) ∈ B := b.property
    have he : (t.val : G) * (b.val : G) = g := congrArg Subtype.val htb
    have hz' : (b.val : G) * z * (b.val : G)⁻¹ ∈ U :=
      (mem_normalizer_iff.mp (hBU hb) z).mp hz
    have hh := (mem_normalizer_iff.mp ((T : Subgroup G).le_normalizer ht)
      ((b.val : G) * z * (b.val : G)⁻¹)).mp (hUT hz')
    rw [←he]
    simpa only [mul_inv_rev,mul_assoc] using hh
  have hWS : W ≤ S := le_pCoreIn_of_normalizes (T.isPGroup'.to_le hWT)
    (hWT.trans (le_inf d.normalizes_L hH.1.1.2)) (le_normalizer_conjugateSpanBy U J)
  exact (le_conjugateSpanBy U J).trans hWS

end CFSG.Quasithin.Chapter13.Section02.A5Outside.OriginalCentralization
