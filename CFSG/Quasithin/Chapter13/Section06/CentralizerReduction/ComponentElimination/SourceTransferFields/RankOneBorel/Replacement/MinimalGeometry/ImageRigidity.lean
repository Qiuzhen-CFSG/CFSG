module

public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceTransferFields.RankOneBorel.Replacement.MinimalGeometry.Transport
public import Theory.SpecificGroups.SL2.SylowUniqueMaximal
public import CFSG.Quasithin.ChapterF.Section01.RankOneBorels.Linear.MatrixBorel
public import Theory.GroupTheory.CComponent.QuotientLifting
public import Theory.GroupTheory.CComponent.QuasisimpleSupplement
public import Theory.GroupTheory.SolvableRadical.SolvableKernel
public import Theory.GroupTheory.SylowNormalIntersection

/-!
# Rank-one image rigidity for the full minimal local choice

Let K belong to the literal family Y_z and let K⁺ be isomorphic to SL₂ over a
finite field of characteristic two. Every local member K₀ ≤ K has K₀* = K*.
Thus the source's choice minimal in all of L(KT_v,T_v) has the required image;
there is no restriction of the minimality predicate to equal-image members.

The original invariance of K supplies a full Sylow of K, hence of K*. The
intersection of (K₀T_v)* with K* contains that Sylow and the nonsolvable image
K₀*. Its image in SL₂ is full, since every proper Sylow overgroup lies in a
solvable Borel. It supplements the solvable radical of K* and contains O₂(K*).
The quasisimple quotient K*/O₂(K*) therefore forces this intersection to be K*.
Finally K₀* is perfect, nontrivial and subnormal there, so C-component minimality
forces K₀* = K*. All action kernels and Sylow transports are derived below.

The universal conclusion of 13.6.14 first supplies invariance of K. Only after
image equality is proved does it supply invariance of K₀, via membership in Y_z.
The existing replacement and common-quotient APIs identify W_K and its moving
commutator and transport the original model with its representative equation.
No natural-module coordinates, block conclusion, or field exclusion is used.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004, the minimal-choice
sentence in 13.6.18, printed p.931 (PDF p.948), using the setup on pp.929–930.
-/

public section

open Subgroup Theory.GroupTheory
open scoped MatrixGroups Pointwise


private theorem proper_subnormal_solvable {A : Type*} [Group A] [Finite A]
    (hA : (⊤ : Subgroup A).IsCComponent) {N : Subgroup A}
    (hN : N.IsSubnormal) (hne : N ≠ ⊤) : Group.IsSolvable N := by
  let e : (⊤ : Subgroup A) ≃* A := topEquiv
  have hp : N.comap e.toMonoidHom ≠ ⊤ := by
    intro ht
    apply hne
    have hm := congrArg (map e.toMonoidHom) ht
    simpa only [map_comap_eq_self_of_surjective (f := e.toMonoidHom) e.surjective,
      map_top_of_surjective e.toMonoidHom e.surjective] using hm
  let := hA.isSolvable_of_subnormal_lt_top (hN.comap e.toMonoidHom) hp
  exact Group.isSolvable_of_surjective
    (e.toMonoidHom.subgroupComap_surjective_of_surjective N e.surjective)

private theorem component_kernel_solvable {A X : Type*} [Group A] [Finite A]
    [Group X] [Nontrivial X] (hA : (⊤ : Subgroup A).IsCComponent)
    (f : A →* X) (hf : Function.Surjective f) : Group.IsSolvable f.ker := by
  apply proper_subnormal_solvable hA (inferInstance : f.ker.Normal).isSubnormal
  intro ht
  obtain ⟨x, hx⟩ := exists_ne (1 : X)
  obtain ⟨a, rfl⟩ := hf x
  have ha : a ∈ f.ker := ht.symm ▸ mem_top a
  exact hx ha

private theorem solvable_of_proper_sylow_overgroup
    {F : Type*} [Field F] [Finite F] [CharP F 2]
    (S : Sylow 2 (SL(2, F))) (M : Subgroup (SL(2, F)))
    (hSM : (S : Subgroup _) ≤ M) (hne : M ≠ ⊤) : Group.IsSolvable M := by
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq (SL(2, F))
    (Matrix.SpecialLinearGroup.upperUnipotentSylow F 2) S
  let e := MulAut.conj g
  let D := M.comap e.toMonoidHom
  have hUD : Matrix.SpecialLinearGroup.upperUnipotent F ≤ D := by
    intro u hu
    apply hSM
    rw [← hg]
    exact mem_map.mpr ⟨u, hu, rfl⟩
  have hD : D ≠ ⊤ := by
    intro ht
    apply hne
    have hm := congrArg (map e.toMonoidHom) ht
    simpa only [D, map_comap_eq_self_of_surjective (f := e.toMonoidHom) e.surjective,
      map_top_of_surjective e.toMonoidHom e.surjective] using hm
  have hDB := Matrix.SpecialLinearGroup.overgroup_le_rankOneBorel hUD hD
  have hb : Matrix.SpecialLinearGroup.rankOneBorel F = BenderSuzuki.Converse.Borel F := by
    rw [← CFSG.Quasithin.ChapterF.Source.Linear.unip_normalizer,
      CFSG.Quasithin.ChapterF.Source.Linear.unip_eq_upper]
  rw [hb] at hDB
  let := CFSG.Quasithin.ChapterF.Source.Linear.borel_solvable (F := F)
  let : Group.IsSolvable D := Group.isSolvable_of_isSolvable_injective (inclusion_injective hDB)
  exact Group.isSolvable_of_surjective
    (e.toMonoidHom.subgroupComap_surjective_of_surjective M e.surjective)

private theorem sylow_overgroup_eq_top
    {A F : Type*} [Group A] [Finite A] [Group.IsPerfect A]
    [Field F] [Finite F] [CharP F 2]
    [IsQuasisimple (A ⧸ pCore 2 A)]
    (hA : (⊤ : Subgroup A).IsCComponent)
    (f : A →* SL(2, F)) (hf : Function.Surjective f)
    (S : Sylow 2 A) (H : Subgroup A) (hSH : (S : Subgroup A) ≤ H)
    (hH : ¬ Group.IsSolvable H) : H = ⊤ := by
  let : Nontrivial (SL(2, F)) := ⟨⟨Matrix.SpecialLinearGroup.transvection
    (i := (0 : Fin 2)) (j := 1) zero_ne_one (1 : F), 1, by
      intro he
      have hh := congrArg (fun g : SL(2, F) => g.val 0 1) he
      simp [Matrix.SpecialLinearGroup.transvection_coe] at hh⟩⟩
  let := component_kernel_solvable hA f hf
  have him : H.map f = ⊤ := by
    by_contra hne
    let := solvable_of_proper_sylow_overgroup (S.mapSurjective hf) (H.map f)
      (map_mono hSH) hne
    let := isSolvable_comap_of_solvable_ker f (H.map f)
    exact hH (Group.isSolvable_of_isSolvable_injective
      (f := inclusion (le_comap_map f H)) (inclusion_injective _))
  have hgen : solvableRadical A ⊔ H = ⊤ := by
    have hcover : H ⊔ f.ker = ⊤ := by
      have hm := congrArg (comap f) him
      simpa only [comap_map_eq, comap_top] using hm
    apply top_unique
    rw [← hcover]
    exact sup_le le_sup_right ((le_solvableRadical f.ker inferInstance inferInstance).trans le_sup_left)
  have hQH : pCore 2 A ≤ H := (pCore_isPGroup.le_sylow_of_normal S).trans hSH
  exact eq_top_of_radical_supplement_of_quasisimple_quotient
    (pCore 2 A) H (hQH.trans H.le_normalizer) hgen

private theorem image_not_solvable {A X : Type*} [Group A] [Group X]
    (f : A →* X) [Group.IsSolvable f.ker] (B : Subgroup A)
    (hB : ¬ Group.IsSolvable B) : ¬ Group.IsSolvable (B.map f) := by
  intro hs
  let := hs
  let := isSolvable_comap_of_solvable_ker f (B.map f)
  exact hB (Group.isSolvable_of_isSolvable_injective
    (f := inclusion (le_comap_map f B)) (inclusion_injective _))

namespace CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceTransferFields.RankOneBorel.Replacement.MinimalGeometry
open ComponentSelection
variable {G : Type*} [Group G] [Finite G]

omit [Finite G] in
private theorem local_top_component (K S : Subgroup G) (hK : K ∈ Chapter1.L G S) :
    (⊤ : Subgroup K).IsCComponent := by
  simpa only [subgroupOf_self] using
    hK.1.subgroupOf_of_le (show K ≤ K from le_rfl) (show K ≤ K ⊔ S from le_sup_left)

private theorem local_sylow_intersection (K S : Subgroup G)
    (hK : K ∈ Chapter1.L G S) (hn : S ≤ normalizer (K : Set G)) :
    ∃ R : Sylow 2 K, (R : Subgroup K).map K.subtype ≤ S := by
  let J := K ⊔ S
  let C := K.subgroupOf J
  let : C.Normal := normal_subgroupOf_of_le_normalizer (sup_le K.le_normalizer hn)
  obtain ⟨P, hP⟩ := hK.2.1
  obtain ⟨R, hR⟩ := P.exists_subgroupOf_eq_of_normal C
  let i : C ≃* K := subgroupOfEquivOfLe le_sup_left
  refine ⟨R.mapSurjective (f := i.toMonoidHom) i.surjective, ?_⟩
  rintro x ⟨k, ⟨r, hr, rfl⟩, rfl⟩
  have hrP : (r : J) ∈ (P : Subgroup J) := by
    change r ∈ (P : Subgroup J).subgroupOf C
    rw [← hR]
    exact hr
  exact hP ▸ mem_map_of_mem J.subtype hrP

/-- Rank-one rigidity uses local membership below K; it does not assume
invariance of the smaller component. -/
theorem starImage_eq_of_local_le
    (K₀ K L T : Subgroup G) (z v : G)
    (hL : Tv T v ≤ normalizer (Lv L v : Set G))
    (hz : Tv T v ≤ centralizer ({z} : Set G))
    (hK : K ∈ Yz L T z v) (hle : K₀ ≤ K)
    (hlocal : K₀ ∈ Chapter1.L G (Tv T v))
    (hnK : Tv T v ≤ normalizer (K : Set G))
    {F : Type*} [Field F] [Finite F] [CharP F 2]
    (e : plusImage K L T z v hL hz K ≃* SL(2, F)) :
    starImage z v K₀ = starImage z v K := by
  let A := starImage z v K
  let g := starImageMap z v K hK.1.1
  have hg : Function.Surjective g := starImageMap_surjective z v K hK.1.1
  let f := e.toMonoidHom.comp (componentStarToPlus K L T z v hK.1.1 hL hz)
  have hf : Function.Surjective f := e.surjective.comp
    (componentStarToPlus_surjective K L T z v hK.1.1 hL hz)
  let : Nontrivial (plusImage K L T z v hL hz K) :=
    (nontrivial_iff_ne_bot _).mpr (plusImage_ne_bot_of_mem_Yz K L T z v hL hz hK)
  let : Nontrivial A :=
    (componentStarToPlus_surjective K L T z v hK.1.1 hL hz).nontrivial
  let : Group.IsSolvable g.ker := component_kernel_solvable
    (local_top_component K (Tv T v) hK.1.2) g hg
  have hA : (⊤ : Subgroup A).IsCComponent := by
    have hm := cComponent_map_of_solvable_ker (local_top_component K (Tv T v) hK.1.2) g hg
    rwa [map_top_of_surjective g hg] at hm
  let : Group.IsPerfect K := Chapter1.mem_L_isPerfect hK.1.2
  let : Group.IsPerfect A := Group.IsPerfect.ofSurjective hg
  let : IsQuasisimple (A ⧸ pCore 2 A) := hK.2.1
  let B := K₀.subgroupOf K
  let E := B.map g
  have hE : E = (starImage z v K₀).subgroupOf A :=
    starImageMap_subgroup z v K₀ K hK.1.1 hle
  have hBns : ¬ Group.IsSolvable B := by
    intro hs
    let := hs
    exact Chapter1.mem_L_not_isSolvable hlocal
      (Group.isSolvable_of_surjective
        (f := (subgroupOfEquivOfLe hle).toMonoidHom) (subgroupOfEquivOfLe hle).surjective)
  have hEns : ¬ Group.IsSolvable E := image_not_solvable g B hBns
  let : Group.IsPerfect K₀ := Chapter1.mem_L_isPerfect hlocal
  let : Group.IsPerfect B := Group.IsPerfect.ofSurjective
    (f := (subgroupOfEquivOfLe hle).symm.toMonoidHom) (subgroupOfEquivOfLe hle).symm.surjective
  let : Group.IsPerfect E := Group.IsPerfect.map g
  let J := K₀ ⊔ Tv T v
  let H := (starImage z v J).subgroupOf A
  have hEH : E ≤ H := by
    rw [hE]
    exact comap_mono (map_mono (comap_mono (show K₀ ≤ J from le_sup_left)))
  have hHns : ¬ Group.IsSolvable H := by
    intro hs
    let := hs
    exact hEns (Group.isSolvable_of_isSolvable_injective
      (f := inclusion hEH) (inclusion_injective hEH))
  obtain ⟨R, hR⟩ := local_sylow_intersection K (Tv T v) hK.1.2 hnK
  let S : Sylow 2 A := R.mapSurjective hg
  have hSH : (S : Subgroup A) ≤ H := by
    rintro x ⟨r, hr, rfl⟩
    have hrT : (r : G) ∈ Tv T v := hR (mem_map_of_mem K.subtype hr)
    exact mem_map.mpr ⟨⟨r, hK.1.1 r.property⟩, (show Tv T v ≤ J from le_sup_right) hrT, rfl⟩
  have hHt : H = ⊤ := sylow_overgroup_eq_top hA f hf S H hSH hHns
  have hAJ : A ≤ starImage z v J := subgroupOf_eq_top.mp hHt
  have hJG : J ≤ Gv v := sup_le (hle.trans hK.1.1) inf_le_right
  have hsJ := hlocal.1.subnormal.map (starImageMap_surjective z v J hJG)
  rw [starImageMap_subgroup z v K₀ J hJG le_sup_left] at hsJ
  have hsE : E.IsSubnormal := by
    rw [hE]
    exact hsJ.comap (inclusion hAJ)
  have hEne : E ≠ ⊥ := by
    intro he
    exact hEns (he.symm ▸ inferInstance)
  have hEt : E = ⊤ := top_unique (hA.minimal E le_top hEne inferInstance hsE)
  apply le_antisymm (map_mono (comap_mono hle))
  exact subgroupOf_eq_top.mp (hE.symm.trans hEt)

/-- The source's full minimal-local choice has the original star image.
Only the universal invariance conclusion of 13.6.14 is an earlier-source input. -/
theorem starImage_eq_of_minimal
    (K₀ K L T : Subgroup G) (z v : G)
    (hL : Tv T v ≤ normalizer (Lv L v : Set G))
    (hz : Tv T v ≤ centralizer ({z} : Set G))
    (hK : K ∈ Yz L T z v) (hle : K₀ ≤ K)
    (hmin : Minimal (fun D => D ∈ Chapter1.LIn (K ⊔ Tv T v) (Tv T v)) K₀)
    (h14 : ∀ D ∈ Yz L T z v, Tv T v ≤ normalizer (D : Set G))
    {F : Type*} [Field F] [Finite F] [CharP F 2]
    (e : plusImage K L T z v hL hz K ≃* SL(2, F)) :
    starImage z v K₀ = starImage z v K :=
  starImage_eq_of_local_le K₀ K L T z v hL hz hK hle hmin.1.2 (h14 K hK) e

/-- Membership and invariance of the replacement follow after image rigidity.
The published replacement theorem then identifies the literal W and moving
commutator subgroups. No invariance assumption is made about K₀. -/
theorem minimal_replacement_consequences
    (K₀ K L T : Subgroup G) (z v : G)
    (hL : Tv T v ≤ normalizer (Lv L v : Set G))
    (hz : Tv T v ≤ centralizer ({z} : Set G))
    (hK : K ∈ Yz L T z v) (hle : K₀ ≤ K)
    (hmin : Minimal (fun D => D ∈ Chapter1.LIn (K ⊔ Tv T v) (Tv T v)) K₀)
    (h14 : ∀ D ∈ Yz L T z v, Tv T v ≤ normalizer (D : Set G))
    {F : Type*} [Field F] [Finite F] [CharP F 2]
    (e : plusImage K L T z v hL hz K ≃* SL(2, F)) :
    starImage z v K₀ = starImage z v K ∧ K₀ ∈ Yz L T z v ∧
      Tv T v ≤ normalizer (K₀ : Set G) ∧
      WK K₀ L T z v = WK K L T z v ∧
      ⁅WK K₀ L T z v, K₀⁆ = ⁅WK K L T z v, K⁆ := by
  have he := starImage_eq_of_minimal K₀ K L T z v hL hz hK hle hmin h14 e
  have hlocal : K₀ ∈ Chapter1.LIn (Gv v) (Tv T v) := ⟨hle.trans hK.1.1, hmin.1.2⟩
  have hY := mem_Yz_of_starImage_eq L T z v hK hlocal he
  have hn₀ := h14 K₀ hY
  have hm := Replacement.replacement_module_eq K₀ K L T z v hK hlocal hn₀ (h14 K hK) he
  exact ⟨he, hY, hn₀, hm.2⟩

/-- The minimal replacement's native plus image has the original marked model.
This uses the published common-quotient transport, with its image-equality and
normalization premises now discharged. -/
noncomputable def modelOfMinimal
    (K₀ K L T : Subgroup G) (z v : G)
    (hL : Tv T v ≤ normalizer (Lv L v : Set G))
    (hz : Tv T v ≤ centralizer ({z} : Set G))
    (hK : K ∈ Yz L T z v) (hle : K₀ ≤ K)
    (hmin : Minimal (fun D => D ∈ Chapter1.LIn (K ⊔ Tv T v) (Tv T v)) K₀)
    (h14 : ∀ D ∈ Yz L T z v, Tv T v ≤ normalizer (D : Set G))
    {F : Type*} [Field F] [Finite F] [CharP F 2]
    (e : plusImage K L T z v hL hz K ≃* SL(2, F)) :
    plusImage K₀ L T z v hL hz K₀ ≃* SL(2, F) :=
  let h := minimal_replacement_consequences K₀ K L T z v hL hz hK hle hmin h14 e
  modelOfEqualStarImage K₀ K L T z v hL hz hK.1.1 hle h.2.2.1 (h14 K hK) h.1 e

/-- Every representative in K₀ retains its original marking in SL₂. -/
theorem modelOfMinimal_mk
    (K₀ K L T : Subgroup G) (z v : G)
    (hL : Tv T v ≤ normalizer (Lv L v : Set G))
    (hz : Tv T v ≤ centralizer ({z} : Set G))
    (hK : K ∈ Yz L T z v) (hle : K₀ ≤ K)
    (hmin : Minimal (fun D => D ∈ Chapter1.LIn (K ⊔ Tv T v) (Tv T v)) K₀)
    (h14 : ∀ D ∈ Yz L T z v, Tv T v ≤ normalizer (D : Set G))
    {F : Type*} [Field F] [Finite F] [CharP F 2]
    (e : plusImage K L T z v hL hz K ≃* SL(2, F)) (k : K₀) :
    modelOfMinimal K₀ K L T z v hL hz hK hle hmin h14 e
      (componentMap K₀ L T z v hL hz k) =
        e (componentMap K L T z v hL hz (inclusion hle k)) := by
  unfold modelOfMinimal
  exact modelOfEqualStarImage_mk K₀ K L T z v hL hz hK.1.1 hle _ _ _ e k

end CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceTransferFields.RankOneBorel.Replacement.MinimalGeometry

end
