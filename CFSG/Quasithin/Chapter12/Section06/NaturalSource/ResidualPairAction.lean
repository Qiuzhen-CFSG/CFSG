module
public import CFSG.Quasithin.Chapter12.Section06.NaturalSource.ResidualCentralizer
public import Theory.GroupTheory.CubicFixedBinaryLayer
public import Theory.GroupTheory.ExtraspecialSquareSubgroupAction

/-!
# The residual on both original singular four-spaces

Extend the pair's conjugation action to its join with L₁. A conjugator
normalizing L₁ makes the latter preserve both original seeds. The core
O₂(H) acts trivially on their central quotient, so the already proved
star centrality becomes centrality of these actual orthogonal actions.
Their restriction to the original pair preserves element orders through
H -> H/O₂(H).

Every original Sylow three-subgroup of L₁ is E₉ and acts faithfully on
both singular four-spaces. A cubic in a restriction kernel has binary
central displacement, hence fixes the corresponding seed upstairs.
C_G(V₅)=C_G(V) and C_L(V)=O₂(L) then make it trivial. Conjugating gives
the second faithfulness statement with the same residual and same g.

This supplies the simultaneous action required by the orthogonal
centralizer argument, but does not yet exclude D₁₀ or establish 12.6.26.
Source: Aschbacher--Smith, proof of 12.6.26, printed pp.831--832.
-/

public section
open Subgroup Theory.GroupTheory
open scoped commutatorElement
namespace CFSG.Quasithin.Chapter12.Section06
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V : Subgroup G} [IsElementaryAbelian 2 V]
  (S : SourceHypothesis KnownSimple.IsKnownSimple T L V)
  (D : OrthogonalMarking L V S.chosen.normalizes) (hZ : ZV L V = ⊥) (z : V)

/-- The original cubic residual is detected on the literal point quotient. -/
theorem SourceHypothesis.original_cubic_detected_on_point_quotient
    (hz : z ≠ 1)
    (hTV : (T : Subgroup G) ≤ normalizer (V : Set G))
    (hTz : (T : Subgroup G) ≤ normalizer ((D.fullSetup hZ T z).V₁ : Set G))
    (hbound : ∀ g : G, g ∉ normalizer (V : Set G) →
      Nat.card (V ⊓ V.map (MulAut.conj g).toMonoidHom : Subgroup G) ≤ 2 ^ 3)
    (a : G) (ha : a ∈ (D.fullSetup hZ T z).L₁) (ha3 : a^3=1)
    (hfix : ∀ w ∈ (D.fullSetup hZ T z).V₅,
      ⁅a,w⁆ ∈ (D.fullSetup hZ T z).V₁) : a=1 := by
  let E := D.fullSetup hZ T z
  have haC : a ∈ L ⊓ E.Gz := (map_subtype_le _) ha
  let : IsElementaryAbelian 2 E.V := E.elementary
  let : IsElementaryAbelian 2 E.V₁ :=
    IsElementaryAbelian.of_le (E.V₁_le_V₅.trans E.V₅_le)
  have hc : a ∈ centralizer (E.V₅ : Set G) := by
    intro w hw
    have hh := cubic_fixed_of_binary_displacement (MulAut.conj a)
      (by rw [←map_pow,ha3,map_one]) E.V₁
      (fun x hx => by change a*x*a⁻¹=x;rw [←haC.2 x hx,mul_inv_cancel_right]) w (hfix w hw)
    exact (mul_inv_eq_iff_eq_mul.mp hh).symm
  rw [S.original_perpendicular_centralizer D hZ z hz hTV hTz hbound] at hc
  have haq : a ∈ L.pCoreIn 2 := S.centralizer_eq_core.le ⟨haC.1,hc⟩
  let : IsElementaryAbelian 3 (zpowers a) := IsElementaryAbelian.zpowers_of_pow_eq_one ha3
  exact Subgroup.disjoint_def.mp ((isPGroup_pCoreIn 2 L).disjoint_of_coprime
    (IsElementaryAbelian.isPGroup 3 (zpowers a)) (by decide)) haq (mem_zpowers a)

/-- The same residual is detected on the second point quotient whenever
the original conjugator normalizes it. -/
theorem SourceHypothesis.original_cubic_detected_on_conjugate_point_quotient
    (hz : z ≠ 1)
    (hTV : (T : Subgroup G) ≤ normalizer (V : Set G))
    (hTz : (T : Subgroup G) ≤ normalizer ((D.fullSetup hZ T z).V₁ : Set G))
    (hbound : ∀ g : G, g ∉ normalizer (V : Set G) →
      Nat.card (V ⊓ V.map (MulAut.conj g).toMonoidHom : Subgroup G) ≤ 2 ^ 3)
    {H : Subgroup G} (hH : H ∈ (D.fullSetup hZ T z).Hz)
    (g : G) (hg : g ∈ H)
    (hgL : g ∈ normalizer ((D.fullSetup hZ T z).L₁ : Set G))
    (a : G) (ha : a ∈ (D.fullSetup hZ T z).L₁) (ha3 : a^3=1)
    (hfix : ∀ w ∈ (D.fullSetup hZ T z).V₅.map (MulAut.conj g).toMonoidHom,
      ⁅a,w⁆ ∈ (D.fullSetup hZ T z).V₁) : a=1 := by
  let E := D.fullSetup hZ T z
  let f := (MulAut.conj g⁻¹).toMonoidHom
  have hgZ : g ∈ normalizer (E.V₁ : Set G) :=
    Subgroup.centralizer_le_normalizer _ (hH.2.1 hg)
  have hZmap : E.V₁.map f=E.V₁ :=
    mem_normalizer_iff_map_conj_eq.mp ((normalizer (E.V₁ : Set G)).inv_mem hgZ)
  have hfa : f a=1 := S.original_cubic_detected_on_point_quotient D hZ z hz hTV hTz hbound
    (f a) ((mem_normalizer_iff.mp ((normalizer (E.L₁ : Set G)).inv_mem hgL) a).mp ha)
    (by rw [←map_pow,ha3,map_one]) (by
      intro w hw
      have hh := hZmap.le (mem_map_of_mem f
        (hfix _ (mem_map_of_mem (MulAut.conj g).toMonoidHom hw)))
      rw [map_commutatorElement] at hh
      have he : f ((MulAut.conj g).toMonoidHom w)=w := by dsimp [f];group
      rwa [he] at hh)
  exact (MulAut.conj g⁻¹).injective (hfa.trans (map_one _).symm)
end CFSG.Quasithin.Chapter12.Section06

namespace CFSG.Quasithin.Chapter12.Section06
open ChapterF.Section09.Setup.Hypothesis
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V : Subgroup G} [IsElementaryAbelian 2 V]
  (S : SourceHypothesis KnownSimple.IsKnownSimple T L V)
  (D : OrthogonalMarking L V S.chosen.normalizes) (hZ : ZV L V = ⊥) (z : V)

/-- The same original residual and pair act together on the actual extraspecial
seed. The two-core acts trivially, so centrality in H-star becomes centrality
of these orthogonal actions. Each original Sylow E-nine acts faithfully on
both original singular four-spaces. -/
theorem SourceHypothesis.original_pair_residual_orthogonal_action
    (hz : z ≠ 1)
    (hTV : (T : Subgroup G) ≤ normalizer (V : Set G))
    (hTz : (T : Subgroup G) ≤ normalizer ((D.fullSetup hZ T z).V₁ : Set G))
    (hbound : ∀ g : G, g ∉ normalizer (V : Set G) →
      Nat.card (V ⊓ V.map (MulAut.conj g).toMonoidHom : Subgroup G) ≤ 2 ^ 3)
    (hns : ∀ w : V, D.Nonsingular w → Gv w.val ≤ M L)
    {H : Subgroup G} (hH : H ∈ (D.fullSetup hZ T z).Hz)
    (hnH : ¬ IsMulCommutative ((D.fullSetup hZ T z).VH H))
    (g : G) (hg : g ∈ H)
    (hgL : g ∈ normalizer ((D.fullSetup hZ T z).L₁ : Set G))
    (hn : ¬ IsPGroup 2 (V ⊔ V.map (MulAut.conj g).toMonoidHom : Subgroup G)) :
    let E := D.fullSetup hZ T z
    let I := V ⊔ V.map (MulAut.conj g).toMonoidHom
    let J := I ⊔ E.L₁
    let P := E.pairSeed g
    ∃ (hs : IsExtraspecial 2 P) (n : J ≤ normalizer (P : Set G)),
      letI := hs
      let α := (ExtraspecialSquare.isometryAction P).comp (seedConjugation J P n)
      let W := ExtraspecialSquare.imageSpace P (E.V₅.subgroupOf P)
      let W' := ExtraspecialSquare.imageSpace P
        ((E.V₅.map (MulAut.conj g).toMonoidHom).subgroupOf P)
      (H.pCoreIn 2).subgroupOf J ≤ α.ker ∧
      (∀ (hIH : I ≤ H) (i : I), orderOf (α (inclusion le_sup_left i)) =
        orderOf (QuotientGroup.mk' (pCore 2 H) (inclusion hIH i))) ∧
      (∀ (i : I) (l : E.L₁),
        Commute (α (inclusion le_sup_left i)) (α (inclusion le_sup_right l))) ∧
      (∀ l : E.L₁, (∀ u ∈ W, (α (inclusion le_sup_right l)).val u ∈ W) ∧
        (∀ u ∈ W', (α (inclusion le_sup_right l)).val u ∈ W')) ∧
      ∀ A : Sylow 3 E.L₁, IsElementaryAbelian 3 A ∧ Nat.card A=9 ∧
        (∀ a : A, (∀ u ∈ W, (α (inclusion le_sup_right a.val)).val u=u) → a=1) ∧
        (∀ a : A, (∀ u ∈ W', (α (inclusion le_sup_right a.val)).val u=u) → a=1) := by
  let E := D.fullSetup hZ T z
  let I := V ⊔ V.map (MulAut.conj g).toMonoidHom
  let J := I ⊔ E.L₁
  let P := E.pairSeed g
  let f := (MulAut.conj g).toMonoidHom
  have h := S.original_f9_of_earlier_geometry D hZ z hz hTV hTz hbound hH
  obtain ⟨hZP,_,hs,_,_⟩ := S.original_non_two_pair_geometry D hZ z hz hTV hTz hbound hns hH g hg hn
  let : IsExtraspecial 2 P := hs
  change (center P).map P.subtype = E.V₁ at hZP
  have hRW : E.L₁ ≤ normalizer (E.V₅ : Set G) := le_sup_left.trans h.local_normalizes
  have hRmap : E.L₁.map f=E.L₁ := mem_normalizer_iff_map_conj_eq.mp hgL
  have hRW' : E.L₁ ≤ normalizer (E.V₅.map f : Set G) := by
    have hh := map_mono (f := f) hRW
    rw [hRmap,map_equiv_normalizer_eq] at hh
    exact hh
  have hRP : E.L₁ ≤ normalizer (P : Set G) :=
    (le_inf hRW hRW').trans (normalizer_inf_normalizer_le_normalizer_sup _ _)
  have hIP : I ≤ normalizer (P : Set G) :=
    h.pair_normalizes_seed_join (E.perpendicular_index hz) g hg hn
  have n : J ≤ normalizer (P : Set G) := sup_le hIP hRP
  have hIH : I ≤ H := sup_le h.V_le_H (by
    rintro _ ⟨v,hv,rfl⟩
    exact H.mul_mem (H.mul_mem hg (h.V_le_H hv)) (H.inv_mem hg))
  have hRH : E.L₁ ≤ H := fun x hx => hH.1.2 (Or.inl hx)
  have hJH : J ≤ H := sup_le hIH hRH
  have hPU : P ≤ E.UH H := sup_le (le_conjugateSpanBy _ _)
    (pair_seed_conjugate_le_closure (D := E.f9 H) g hg)
  let α := (ExtraspecialSquare.isometryAction P).comp (seedConjugation J P n)
  have hk : (H.pCoreIn 2).subgroupOf J ≤ α.ker := by
    intro x hx
    apply (ExtraspecialSquare.isometryAction_eq_one_iff P _).mpr
    ext u
    obtain ⟨p,rfl⟩ := QuotientGroup.mk'_surjective (center P) u
    rw [quotientAut_apply_mk]
    apply QuotientGroup.eq_iff_div_mem.mpr
    have hc : ⁅(x:G),(p:G)⁆ ∈ E.V₁ := by
      rw [←commutatorElement_inv]
      exact E.V₁.inv_mem (h.commutator_UH_QH_le_point
        (commutator_mem_commutator (hPU p.property) hx))
    have he : (seedConjugation J P n x p / p : G)=⁅(x:G),(p:G)⁆ := by
      simp only [seedConjugation_apply,div_eq_mul_inv,commutatorElement_def,Subgroup.coe_inv]
    have hc' : seedConjugation J P n x p / p ∈ E.V₁.subgroupOf P := by
      change (seedConjugation J P n x p : G) / (p : G) ∈ E.V₁
      rwa [he]
    rw [←hZP,subgroupOf,comap_map_eq_self_of_injective P.subtype_injective] at hc'
    exact hc'
  have hcomm := S.original_normalizing_pair_centralizes_residual D hZ z hz hTV hTz hbound hH hnH g hg hgL
  obtain ⟨hIH',n',β,e,hβ,_,hproj,_⟩ :=
    S.original_non_two_pair_square_action_of_extraspecial D hZ z hz hTV hTz hbound hns hH g hg hn hs
  have hord (hIH : I ≤ H) (i : I) : orderOf (α (inclusion le_sup_left i)) =
      orderOf (QuotientGroup.mk' (pCore 2 H) (inclusion hIH i)) := by
    let r : Nonabelian.Setup.star H I :=
      ⟨QuotientGroup.mk' (pCore 2 H) (inclusion hIH i),mem_map_of_mem _ i.property⟩
    have he : (e r).val = α (inclusion le_sup_left i) :=
      (hproj i).trans (by rw [hβ];rfl)
    calc
      orderOf (α (inclusion le_sup_left i)) = orderOf (e r).val := congrArg orderOf he.symm
      _ = orderOf (e r) := Subgroup.orderOf_coe _
      _ = orderOf r := e.orderOf_eq _
      _ = _ := (Subgroup.orderOf_coe r).symm
  refine ⟨hs,n,hk,hord,?_,?_,?_⟩
  · intro i l
    let iJ : J := inclusion le_sup_left i
    let lJ : J := inclusion le_sup_right l
    let q : J →* (H ⧸ pCore 2 H) :=
      (QuotientGroup.mk' (pCore 2 H)).comp (inclusion hJH)
    have hc : Commute (q iJ) (q lJ) :=
      (hcomm (mem_map_of_mem _ i.property) _ (mem_map_of_mem _ l.property)).symm
    have hcq : q ⁅iJ,lJ⁆=1 := by
      rw [map_commutatorElement,commutatorElement_eq_one_iff_mul_comm]
      exact hc.eq
    have hcm : ⁅iJ,lJ⁆ ∈ (H.pCoreIn 2).subgroupOf J := by
      have hh := (QuotientGroup.eq_one_iff (inclusion hJH ⁅iJ,lJ⁆)).mp hcq
      exact mem_map_of_mem H.subtype hh
    have hh := hk hcm
    change α ⁅iJ,lJ⁆=1 at hh
    rw [map_commutatorElement,commutatorElement_eq_one_iff_mul_comm] at hh
    exact hh
  · intro l
    constructor
    · apply ExtraspecialSquare.preserves_imageSpace
      intro w hw
      exact (mem_normalizer_iff.mp (hRW l.property) w.val).mp hw
    · apply ExtraspecialSquare.preserves_imageSpace
      intro w hw
      exact (mem_normalizer_iff.mp (hRW' l.property) w.val).mp hw
  · intro A
    obtain ⟨hA,hcard⟩ := S.original_point_residual_sylow D hZ z hz hTz A
    let := hA
    have hcube (a : A) : ((a.val : E.L₁) : G)^3=1 :=
      congrArg (fun b : A => (b.val : G))
        (Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
          (IsElementaryAbelian.exponent_dvd_p 3 A) a)
    refine ⟨hA,hcard,?_,?_⟩
    · intro a ha
      have hf := (ExtraspecialSquare.fixes_imageSpace_iff P
        (seedConjugation J P n (inclusion le_sup_right a.val)) (E.V₅.subgroupOf P)).mp ha
      apply Subtype.ext
      apply Subtype.ext
      apply S.original_cubic_detected_on_point_quotient D hZ z hz hTV hTz hbound
        (a.val : G) a.val.property (hcube a)
      intro w hw
      have hh := hZP.le (mem_map_of_mem P.subtype (hf ⟨w,mem_sup_left hw⟩ hw))
      simpa only [map_div,coe_subtype,seedConjugation_apply,coe_inclusion,
        div_eq_mul_inv,commutatorElement_def,Subgroup.coe_mul,Subgroup.coe_inv] using hh
    · intro a ha
      have hf := (ExtraspecialSquare.fixes_imageSpace_iff P
        (seedConjugation J P n (inclusion le_sup_right a.val))
        ((E.V₅.map f).subgroupOf P)).mp ha
      apply Subtype.ext
      apply Subtype.ext
      apply S.original_cubic_detected_on_conjugate_point_quotient D hZ z hz hTV hTz hbound
        hH g hg hgL (a.val : G) a.val.property (hcube a)
      intro w hw
      have hh := hZP.le (mem_map_of_mem P.subtype (hf ⟨w,mem_sup_right hw⟩ hw))
      simpa only [map_div,coe_subtype,seedConjugation_apply,coe_inclusion,
        div_eq_mul_inv,commutatorElement_def,Subgroup.coe_mul,Subgroup.coe_inv] using hh
end CFSG.Quasithin.Chapter12.Section06
