module
public import CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.OrdinaryRecognitionExclusions
public import CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.FiveLocalFF.LinearThree
public import Theory.GroupTheory.PerfectCentralQuotientNormalizer

/-!
# Full-Sylow placement and the original ordinary PSL₃ exclusion

Restrict the given C-component from H ∩ N_G(L) to the join of L with
S ∩ K, retaining the actual embeddings into K. Thus L is a local
C-component for that full Sylow subgroup. A central quotient preserves
this property; perfectness of K and escape from N_G(L) keep its image proper.

In a binary PSL₃ model the full-Sylow local-component theorem now constructs
both possible parabolic-residual markings. The actual R₀ involution excludes
them by pointwise rigidity. This discharges the linear row without a local
placement callback, including the legitimate L₃(4) row and its central covers.

The remaining ordinary rows and construction of OrdinarySymplecticMarking
are not asserted here. Source: Aschbacher--Smith C.3.1, pp.149--151,
and 4.3.6, printed p.614, using the earlier A.3 local-component geometry.
-/

public section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
namespace SourceConfiguration

omit [Finite G] in
/-- The original L belongs to the local C-component family of the unchanged S ∩ K. -/
theorem ordinaryLocal_mem_localCComponents (c : SourceConfiguration T L)
    (D : Chapter12.Section02.ChosenModule T L V) :
    c.ordinaryLocal ∈ ChapterA.Section03.localCComponents (c.ordinarySylowInH.subgroupOf c.K) := by
  let f := c.H.subtype.comp c.K.subtype
  have hf : Function.Injective f := c.H.subtype_injective.comp c.K.subtype_injective
  let X := c.ordinaryLocal ⊔ c.ordinarySylowInH.subgroupOf c.K
  let J := X.map f
  have hLJ : L ≤ J := by
    intro l hl
    let lH : c.H := ⟨l,c.le_I.trans c.I_le_H hl⟩
    let lK : c.K := ⟨lH,c.ordinaryLocal_le hl⟩
    exact ⟨lK,(le_sup_left : c.ordinaryLocal ≤ X) hl,rfl⟩
  have hJM : J ≤ c.H ⊓ normalizer (L : Set G) := by
    apply map_le_iff_le_comap.mpr
    apply sup_le
    · intro k hk
      exact c.c28.component_le hk
    · intro k hk
      exact ⟨(k : c.H).property,D.sylow_normalizes_component hk.1⟩
  have hc := c.c28.component.subgroupOf_of_le hLJ hJM
  let e : X ≃* J := X.equivMapOfInjective f hf
  have he : (L.subgroupOf J).map e.symm.toMonoidHom = c.ordinaryLocal.subgroupOf X := by
    ext x
    constructor
    · rintro ⟨y,hy,rfl⟩
      change f (e.symm y) ∈ L
      have hyval : f (e.symm y) = (y : G) := congrArg Subtype.val (e.apply_symm_apply y)
      rwa [hyval]
    · intro hx
      exact ⟨e x,hx,e.symm_apply_apply x⟩
  change (c.ordinaryLocal.subgroupOf X).IsCComponent
  rw [←he]
  exact hc.map_equiv e.symm

/-- The same full Sylow and local C-component survive every actual central-quotient marking. -/
theorem ordinary_model_local_data (c : SourceConfiguration T L)
    (D : Chapter12.Section02.ChosenModule T L V) (ho : IsComponent c.H c.K)
    {S : Type*} [Group S] (e : (c.K ⧸ center c.K) ≃* S) :
    let f := e.toMonoidHom.comp (QuotientGroup.mk' (center c.K))
    ∃ P : Sylow 2 c.K,
      (P : Subgroup c.K) = c.ordinarySylowInH.subgroupOf c.K ∧
      c.ordinaryLocal.map f ∈ ChapterA.Section03.localCComponents
        (P.mapSurjective (f := f) (e.surjective.comp (QuotientGroup.mk'_surjective (center c.K))) : Subgroup S) ∧
      c.ordinaryLocal.map f ≠ ⊤ := by
  let := ho.2
  let f := e.toMonoidHom.comp (QuotientGroup.mk' (center c.K))
  have hk : f.ker = center c.K := by
    ext k
    change e (QuotientGroup.mk' (center c.K) k) = 1 ↔ k ∈ center c.K
    rw [←map_one e,e.injective.eq_iff]
    exact QuotientGroup.eq_one_iff k
  let : Group.IsSolvable f.ker := by
    rw [hk]
    exact Group.isSolvable_of_comm fun x y => mul_comm x y
  obtain ⟨P,hP⟩ := c.ordinary_component_sylow
  refine ⟨P,hP,?_,?_⟩
  · have hl := c.ordinaryLocal_mem_localCComponents D
    rw [←hP] at hl
    exact Chapter1.Section02.localCComponents_map_of_solvable_ker hl f
  · intro he
    have ht : (⊤ : Subgroup c.K) ≤ c.ordinaryLocal :=
      perfect_le_of_map_le_of_central_kernel f (by rw [hk]) ⊤ c.ordinaryLocal
        (by rw [he]; exact le_top)
    have hKL : c.K.map c.H.subtype ≤ L := by
      rintro _ ⟨k,hk,rfl⟩
      exact ht (show (⟨k,hk⟩ : c.K) ∈ (⊤ : Subgroup c.K) from trivial)
    exact c.component_outside (hKL.trans L.le_normalizer)

/-- Actual PSL₃ exclusion, including q=4 and all central covers: the local pair
is constructed from the original full Sylow, rather than assumed as a marking. -/
theorem ordinary_no_pslThree (c : SourceConfiguration T L)
    (D : Chapter12.Section02.ChosenModule T L V) (ho : IsComponent c.H c.K)
    {F : Type*} [Field F] [Finite F] [CharP F 2]
    {n : ℕ} (hn : 1 < n) (hF : Nat.card F = 2 ^ n)
    (e : (c.K ⧸ center c.K) ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 3) F) : False := by
  let f := e.toMonoidHom.comp (QuotientGroup.mk' (center c.K))
  obtain ⟨P,_,hlocal,hproper⟩ := c.ordinary_model_local_data D ho e
  let S := P.mapSurjective (f := f) (e.surjective.comp (QuotientGroup.mk'_surjective (center c.K)))
  obtain ⟨g,hg⟩ := ChapterA.Section03.SourceEmbeddings.FiveLocalFF.linear_three_local_placement
    hF hn S (c.ordinaryLocal.map f) hlocal hproper
  apply c.ordinary_no_pslThree_parabolic_marking D ho (by omega) hF (e.trans (MulAut.conj g))
  have he : (e.trans (MulAut.conj g)).toMonoidHom =
      (MulAut.conj g).toMonoidHom.comp e.toMonoidHom := by ext; rfl
  simpa only [f,map_map,he,MonoidHom.comp_assoc] using hg

end SourceConfiguration
end CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness
