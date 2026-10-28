module
public import Theory.GroupTheory.UniqueFixedCosetMaximalNormalizer
public import Theory.ElementaryAbelian.Injective
public import CFSG.Quasithin.ChapterI.Section06To08.UniqueFixedSource

/-!
# Full I.8.5 in the maximal unitary short-line quotient

If the short-root stabilizer X is proper, choose W maximal between the
central involution and its elementary fixed line U with N(W) escaping X.
Pointwise Sylow-subgroup fusion supplies unique fixed cosets for every
nonzero element of U/W. We check elementary abelianness, relative normality,
nontriviality and properness in the literal N(W)/W, and apply both clauses
of I.8.5 there, retaining its full Bender/Borel and automizer conclusions.

This supplies the maximal-W section of Aschbacher–Smith F.4.42, printed
p.296. Excluding its alternatives still needs the odd-core and perfect-actor
arguments. It does not itself assert ambient short-centralizer containment.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.ChapterF.UnitarySource
variable {G : Type*} [Group G] [Finite G]

/-- The actual maximal-W quotient satisfies all hypotheses of full I.8.5. -/
theorem maximal_normalizer_section
    (X U Z : Subgroup G) [IsElementaryAbelian 2 U]
    (hX : X ≠ ⊤) (hUX : U ≤ X) (hZU : Z ≤ U) (hZ : Z ≤ center G)
    (hNU : normalizer (U : Set G) = X)
    (P : Sylow 2 G) (hPX : (P : Subgroup G) ≤ X)
    (z : G) (hzP : z ∈ (P : Subgroup G))
    (hzcentral : ∀ a ∈ (P : Subgroup G), Commute z a)
    (hfix : ∃! q : G ⧸ X, z • q = q) :
    ∃ W : Subgroup G, Z ≤ W ∧ W < U ∧ ¬ normalizer (W : Set G) ≤ X ∧
      (∀ R : Subgroup G, W < R → R ≤ U → normalizer (R : Set G) ≤ X) ∧
      let N := normalizer (W : Set G)
      let f := QuotientGroup.mk' (W.subgroupOf N)
      let V := (U.subgroupOf N).map f
      let Y := (X.subgroupOf N).map f
      V ≠ ⊥ ∧ Y ≠ ⊤ ∧ normalizer (V : Set (N ⧸ W.subgroupOf N)) = Y ∧
      IsElementaryAbelian 2 V ∧
      ∃ hnormal : (V.subgroupOf Y).Normal, letI := hnormal;
      (∀ v ∈ V, v ≠ 1 → ∃! q : (N ⧸ W.subgroupOf N) ⧸ Y, v • q = q) ∧
      (let K := normalClosure (V : Set (N ⧸ W.subgroupOf N))
       (Nat.card V = 2 ∧ pPrimeCore 2 K ⊔ V.subgroupOf K = ⊤) ∨
         (IsQuasisimple K ∧ BenderSuzuki.IsSimpleBenderGroup (K ⧸ center K) ∧
           Y.comap K.subtype = normalizer (V.subgroupOf K : Set K) ∧
           BenderSuzuki.IsBorelSubgroup (Y.comap K.subtype) ∧
           ∃ S : Sylow 2 K, (S : Subgroup K) ≤ Y.comap K.subtype ∧
             V.subgroupOf K = (omega₁ S (p := 2)).map (S : Subgroup K).subtype)) ∧
      Group.IsSolvable (Y ⧸ centralizer (V.subgroupOf Y : Set Y)) := by
  obtain ⟨W,hZW,hWU,hWX,hmax⟩ :=
    UniqueFixedCoset.exists_maximal_normalizer_escape X U Z hX hZU hZ hNU
  have hXU : X ≤ normalizer (U : Set G) := hNU.ge
  let : (U.subgroupOf X).Normal := normal_subgroupOf_of_le_normalizer hXU
  have hUP : U ≤ P := by
    intro u hu
    have hpU : IsPGroup 2 (U.subgroupOf X) :=
      (IsElementaryAbelian.isPGroup 2 U).comap_subtype
    exact hpU.le_sylow_of_normal
      (P.subtype hPX) (show (⟨u,hUX hu⟩ : X) ∈ U.subgroupOf X from hu)
  let N := normalizer (W : Set G)
  let f := QuotientGroup.mk' (W.subgroupOf N)
  let V := (U.subgroupOf N).map f
  let Y := (X.subgroupOf N).map f
  have hUN : U ≤ N := by
    intro u hu
    apply Subgroup.centralizer_le_normalizer
    intro w hw
    exact congrArg Subtype.val (mul_comm (⟨w,hWU.le hw⟩ : U) ⟨u,hu⟩)
  have hVY : V ≤ Y := map_mono (comap_mono hUX)
  have hnorm : Y ≤ normalizer (V : Set (N ⧸ W.subgroupOf N)) :=
    (map_mono ((comap_mono hXU).trans (le_normalizer_comap N.subtype))).trans
      (le_normalizer_map f)
  let : (V.subgroupOf Y).Normal := normal_subgroupOf_of_le_normalizer hnorm
  let : IsElementaryAbelian 2 (U.subgroupOf N) := IsElementaryAbelian.subgroupOf hUN
  let : IsElementaryAbelian 2 V := IsElementaryAbelian.map f
  have hVne : V ≠ ⊥ := by
    intro he
    have hUW : U ≤ W := by
      intro u hu
      have hh : f ⟨u,hUN hu⟩ ∈ V := mem_map_of_mem f hu
      rw [he,mem_bot] at hh
      exact (QuotientGroup.eq_one_iff (N := W.subgroupOf N) ⟨u,hUN hu⟩).mp hh
    exact (not_le_of_gt hWU) hUW
  have hker : f.ker ≤ X.subgroupOf N := by
    rw [QuotientGroup.ker_mk']
    exact comap_mono (hWU.le.trans hUX)
  have hYne : Y ≠ ⊤ := by
    intro he
    have hh := congrArg (comap f) he
    rw [comap_map_eq_self hker,comap_top] at hh
    exact hWX (fun a ha => hh.ge (show (⟨a,ha⟩ : N) ∈ (⊤ : Subgroup N) from mem_top _))
  have hNUbar : normalizer (V : Set (N ⧸ W.subgroupOf N)) = Y := by
    have hf : f.range = ⊤ := MonoidHom.range_eq_top.mpr (QuotientGroup.mk'_surjective _)
    have hkU : f.ker ≤ U.subgroupOf N := by
      rw [QuotientGroup.ker_mk']
      exact comap_mono hWU.le
    have he : (normalizer (V : Set (N ⧸ W.subgroupOf N))).comap f = X.subgroupOf N := by
      rw [comap_normalizer_eq_of_le_range (show V ≤ f.range from hf ▸ le_top)]
      change normalizer ((U.subgroupOf N).map f |>.comap f : Set N) = _
      rw [comap_map_eq_self hkU,←subgroupOf_normalizer_eq hUN,hNU]
    have he' := congrArg (map f) he
    rw [map_comap_eq_self (show normalizer (V : Set (N ⧸ W.subgroupOf N)) ≤ f.range from
      hf ▸ le_top)] at he'
    exact he'
  have hu := UniqueFixedCoset.maximal_normalizer_fixed_cosets P hPX hzP hzcentral
    hfix U W hUP hXU hWU.le hmax
  obtain ⟨hstructure,hsolvable⟩ := ChapterI.Section06To08.lemma_I_8_5 V Y hVY hVne hYne hu
  exact ⟨W,hZW,hWU,hWX,hmax,hVne,hYne,hNUbar,inferInstance,inferInstance,hu,hstructure,hsolvable⟩

end CFSG.Quasithin.ChapterF.UnitarySource
