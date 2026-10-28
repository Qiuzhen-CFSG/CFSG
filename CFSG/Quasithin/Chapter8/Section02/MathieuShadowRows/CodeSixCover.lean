module
public import CFSG.Quasithin.Chapter8.Section02.MathieuShadowRows.CodeComponentModels
public import CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.SixLocalFF.BinaryLinear
public import CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.Restriction
public import Theory.Alternating.OddCentralCovers
public import Theory.GroupTheory.PCoreFrattiniTransport
public import Theory.Mathieu.M11.Properties.Order

/-!
# The full A₆ section in the exceptional Xi component models

The center of an A₆ cover modulo its full two-core is odd, and the
alternating covering theorem bounds it by three. In M₁₁, PSL₄(2), and
PSL₅(2), an embedded section cannot retain the cubic center: its order
would then be divisible by 27, contrary to the containing model's order.
The argument uses the actual inclusion and quotient maps and does not
assume that the smaller two-core equals the ambient two-core.

The resulting full A₆ marking supplies the exact premise of the existing
binary-linear local-section exclusions. Restriction retains the original
full Sylow and the smaller C-component. The original Chapter12 application
is M22CodeSixSection; the Held alternative is not covered by this argument.

Source: Aschbacher--Smith 8.2.2(1), printed p.715, using A.3.12(4--5)
and the alternating central-cover theorem, refs/quasithin.pdf.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter8.MathieuShadowRows
open Chapter1.XiEmbedding
variable {G : Type*} [Group G] [Finite G]

private theorem exceptional_not_twentyseven {Q : Type*} [Group Q]
    (h : ExceptionalModel Q) : ¬ 27 ∣ Nat.card Q := by
  rcases h with h | h | h
  · obtain ⟨e⟩ := h
    rw [Nat.card_congr e.toEquiv,Sporadic.Mathieu.m11_order]
    decide
  · obtain ⟨F,_,_,hF,⟨e⟩⟩ := h
    have hc := Atlas.ExceptionalSupport.card_psl_mul (F := F) 4
    rw [hF] at hc
    rw [Nat.card_congr e.toEquiv]
    norm_num [Fin.prod_univ_succ] at hc
    rw [hc]
    decide
  · obtain ⟨F,_,_,hF,⟨e⟩⟩ := h
    have hc := Atlas.ExceptionalSupport.card_psl_mul (F := F) 5
    rw [hF] at hc
    rw [Nat.card_congr e.toEquiv]
    norm_num [Fin.prod_univ_succ] at hc
    rw [hc]
    decide

private theorem core_quotient_center_odd [IsQuasisimple (G ⧸ pCore 2 G)] :
    Odd (Nat.card (center (G ⧸ pCore 2 G))) := by
  let Q := G ⧸ pCore 2 G
  let : IsQuasisimple (⊤ : Subgroup Q) := IsQuasisimple.of_mulEquiv topEquiv.symm
  have ho := GLS3.Chapter5.OddCentralCovers.component_center_odd
    (pCore_quotient_pCore_eq_bot (G := G) 2) ⊤ ⟨IsSubnormal.top,inferInstance⟩
  rwa [Nat.card_congr (centerCongr (topEquiv : (⊤ : Subgroup Q) ≃* Q)).toEquiv] at ho

/-- In an exceptional Xi component, an embedded projective A₆ section has no remaining covering center. -/
theorem projective_six_core_equiv_of_exceptional_embedding
    {R : Type*} [Group R] [Finite R] [IsQuasisimple (R ⧸ pCore 2 R)]
    (e : ((R ⧸ pCore 2 R) ⧸ center (R ⧸ pCore 2 R)) ≃* alternatingGroup (Fin 6))
    (f : R →* G) (hf : Function.Injective f)
    (hm : ExceptionalModel (G ⧸ pCore 2 G)) :
    Nonempty ((R ⧸ pCore 2 R) ≃* alternatingGroup (Fin 6)) := by
  let q := (QuotientGroup.mk' (pCore 2 G)).comp f
  have hk : IsPGroup 2 q.rangeRestrict.ker := by
    rw [MonoidHom.ker_rangeRestrict,←MonoidHom.comap_ker,QuotientGroup.ker_mk']
    exact pCore_isPGroup.comap_of_injective f hf
  let a := q.rangeRestrict.pCoreQuotientEquiv q.rangeRestrict_surjective hk
  have hd : Nat.card (R ⧸ pCore 2 R) ∣ Nat.card (G ⧸ pCore 2 G) := by
    rw [Nat.card_congr a.toEquiv]
    exact (card_quotient_dvd_card _).trans q.range.card_subgroup_dvd_card
  rcases GLS3.Chapter5.OddCentralCovers.odd_center_alternatives 6 (by decide) e
    core_quotient_center_odd with hc | ⟨_,hc⟩
  · exact ⟨GLS3.Chapter5.OddCentralCovers.alternatingEquivOfCenterCardOne 6 e hc⟩
  · have hh : 27 ∣ Nat.card (R ⧸ pCore 2 R) := by
      rw [card_eq_card_quotient_mul_card_subgroup (center (R ⧸ pCore 2 R)),
        hc,Nat.card_congr e.toEquiv,nat_card_alternatingGroup,Nat.card_fin]
      decide
    exact (exceptional_not_twentyseven hm (hh.trans hd)).elim

/-- Both binary higher-linear alternatives are impossible for the original local projective A₆ section. The center is removed using the actual embedding. -/
theorem not_binary_containing_projective_six
    (S : Sylow 2 G) {B K : Subgroup G}
    (hB : B ∈ ChapterA.Section03.localCComponents S)
    (hK : K.IsCComponent) (hBK : B ≤ K)
    [IsQuasisimple (B ⧸ pCore 2 B)]
    (e : ((B ⧸ pCore 2 B) ⧸ center (B ⧸ pCore 2 B)) ≃* alternatingGroup (Fin 6))
    {n : ℕ} (hn : n = 4 ∨ n = 5)
    (hm : ClassicalGroup.IsPSL (K ⧸ pCore 2 K) n 2) : False := by
  have hex : ExceptionalModel (K ⧸ pCore 2 K) := by
    rcases hn with rfl | rfl
    · exact Or.inr (Or.inl hm)
    · exact Or.inr (Or.inr hm)
  obtain ⟨eB⟩ := projective_six_core_equiv_of_exceptional_embedding e
    (inclusion hBK) (inclusion_injective hBK) hex
  obtain ⟨T,hT,hl⟩ := ChapterA.Section03.SourceEmbeddings.exists_local_sylow_restriction
    S hB hBK hK.subnormal
  let A := B.subgroupOf K
  let q := QuotientGroup.mk' (pCore 2 K)
  let a : A ≃* B := subgroupOfEquivOfLe hBK
  let aq := QuotientGroup.congr _ _ a (pCore_map_iso 2 a)
  have hk : IsPGroup 2 (q.subgroupMap A).ker := by
    rw [Subgroup.ker_subgroupMap,QuotientGroup.ker_mk']
    exact pCore_isPGroup.comap_subtype
  let b := (q.subgroupMap A).pCoreQuotientEquiv (q.subgroupMap_surjective A) hk
  let : Group.IsSolvable q.ker := by
    rw [QuotientGroup.ker_mk']
    let := pCore_isNilpotent (p := 2) (G := K)
    infer_instance
  exact ChapterA.Section03.SourceEmbeddings.SixLocalFF.BinaryLinear.not_section_binary_linear
    (T.mapSurjective (QuotientGroup.mk'_surjective _)) (A.map q)
    (Chapter1.Section02.localCComponents_map_of_solvable_ker hl q)
    (b.symm.trans (aq.trans eB)) hn hm

end CFSG.Quasithin.Chapter8.MathieuShadowRows
