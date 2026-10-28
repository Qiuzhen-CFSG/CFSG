module
public import CFSG.Quasithin.ChapterD.Section01.UniqueFactor.Setup
public import Theory.GroupTheory.PCoreLocalSetup
public import Theory.GroupTheory.SylowNormalIntersection
/-!
# The normalizer of the Sylow centralizer preserves the full action

If M normalizes V and contains a Sylow two-subgroup T of the ambient
group, the Frattini argument in C_M(V) writes M as the product of
N_M(C_T(V)) and C_M(V). The normalizer therefore has exactly the same
conjugation image on V. If this image has trivial two-core, then the
normalizer's two-core is precisely C_T(V).

These identities retain the original ambient subgroups and establish
the full-module input to Aschbacher--Smith 3.2.5--6, printed pp.580--581.
-/

public section
open Subgroup
open scoped IsMulCommutative
namespace CFSG.Quasithin.ChapterD.UniqueFactor
variable {G : Type*} [Group G] [Finite G]

abbrev centralizerSylowNormalizer (T : Sylow 2 G) (M V : Subgroup G) : Subgroup G :=
  M ⊓ normalizer ((T : Subgroup G) ⊓ centralizer (V : Set G) : Set G)

omit [Finite G] in
theorem sylow_le_centralizerSylowNormalizer (T : Sylow 2 G) (M V : Subgroup G)
    (hTM : (T : Subgroup G) ≤ M) (hn : M ≤ normalizer (V : Set G)) :
    (T : Subgroup G) ≤ centralizerSylowNormalizer T M V := by
  refine le_inf hTM ?_
  exact (le_inf (T : Subgroup G).le_normalizer
    ((hTM.trans hn).trans (normalizer_le_normalizer_centralizer _))).trans
      inf_normalizer_le_normalizer_inf

theorem centralizerSylowNormalizer_factorization (T : Sylow 2 G) (M V : Subgroup G)
    (hTM : (T : Subgroup G) ≤ M) (hn : M ≤ normalizer (V : Set G)) :
    ∀ m ∈ M, ∃ n ∈ centralizerSylowNormalizer T M V,
      ∃ c ∈ M ⊓ centralizer (V : Set G), m = n*c := by
  let C := (centralizer (V : Set G)).subgroupOf M
  let : C.Normal := normal_subgroupOf_of_le_normalizer
    (hn.trans (normalizer_le_normalizer_centralizer _))
  obtain ⟨P,hP⟩ := (T.subtype hTM).exists_subgroupOf_eq_of_normal C
  let R := (P : Subgroup C).map C.subtype
  have hR : R.map M.subtype = (T : Subgroup G) ⊓ centralizer (V : Set G) := by
    rw [show R = (P : Subgroup C).map C.subtype from rfl,hP,map_map]
    ext x
    constructor
    · rintro ⟨c,hc,rfl⟩
      exact ⟨hc,c.property⟩
    · intro hx
      exact ⟨⟨⟨x,hTM hx.1⟩,hx.2⟩,hx.1,rfl⟩
  have hf : normalizer (R : Set M) ⊔ C = ⊤ := P.normalizer_sup_eq_top
  intro m hm
  have hm' : (⟨m,hm⟩ : M) ∈ normalizer (R : Set M) ⊔ C := hf ▸ mem_top _
  obtain ⟨n,hn',c,hc,he⟩ := mem_sup_of_normal_right.mp hm'
  have hnR : (n : G) ∈ normalizer (R.map M.subtype : Set G) :=
    R.le_normalizer_map M.subtype (mem_map_of_mem M.subtype hn')
  rw [hR] at hnR
  exact ⟨n,⟨n.property,hnR⟩,c,⟨c.property,hc⟩,(congrArg Subtype.val he).symm⟩

theorem centralizerSylowNormalizer_actionImage_eq (T : Sylow 2 G) (M V : Subgroup G)
    (hTM : (T : Subgroup G) ≤ M) (hn : M ≤ normalizer (V : Set G)) :
    internalActionImage (centralizerSylowNormalizer T M V) V (inf_le_left.trans hn) =
      internalActionImage M V hn := by
  apply le_antisymm
  · rintro a ⟨n,rfl⟩
    exact ⟨⟨n,n.property.1⟩,rfl⟩
  · rintro a ⟨m,rfl⟩
    obtain ⟨n,hn',c,hc,he⟩ := centralizerSylowNormalizer_factorization T M V hTM hn m m.property
    let nn : M := ⟨n,hn'.1⟩
    let cc : M := ⟨c,hc.1⟩
    have hm : m = nn * cc := Subtype.ext he
    have hcc : actionHom M V hn cc = 1 := by
      apply MonoidHom.mem_ker.mp
      rw [actionHom_ker]
      exact hc.2
    refine ⟨⟨n,hn'⟩,?_⟩
    change actionHom M V hn nn = actionHom M V hn m
    rw [hm,map_mul,hcc,mul_one]

theorem centralizerSylowNormalizer_image_reduced (T : Sylow 2 G) (M V : Subgroup G)
    (hTM : (T : Subgroup G) ≤ M) (hn : M ≤ normalizer (V : Set G))
    (hred : pCore 2 (internalActionImage M V hn) = ⊥) :
    pCore 2 (internalActionImage (centralizerSylowNormalizer T M V) V
      (inf_le_left.trans hn)) = ⊥ := by
  let e := MulEquiv.subgroupCongr (centralizerSylowNormalizer_actionImage_eq T M V hTM hn)
  have he := pCore_map_iso 2 e
  rw [hred] at he
  exact (Subgroup.map_eq_bot_iff_of_injective _ e.injective).mp he

theorem centralizerSylowNormalizer_core (T : Sylow 2 G) (M V : Subgroup G)
    (hTM : (T : Subgroup G) ≤ M) (hn : M ≤ normalizer (V : Set G))
    (hred : pCore 2 (internalActionImage M V hn) = ⊥) :
    (centralizerSylowNormalizer T M V).pCoreIn 2 =
      (T : Subgroup G) ⊓ centralizer (V : Set G) := by
  let N := centralizerSylowNormalizer T M V
  let R := (T : Subgroup G) ⊓ centralizer (V : Set G)
  let f := actionHom N V (inf_le_left.trans hn)
  have hf := centralizerSylowNormalizer_image_reduced T M V hTM hn hred
  have hc : (pCore 2 N).map f.rangeRestrict ≤ pCore 2 f.range :=
    le_sSup ⟨Normal.map inferInstance _ f.rangeRestrict_surjective,pCore_isPGroup.map _⟩
  change pCore 2 f.range = ⊥ at hf
  rw [hf] at hc
  have hk : pCore 2 N ≤ f.ker := by
    have hh := (map_eq_bot_iff (pCore 2 N)).mp (bot_unique hc)
    simpa only [MonoidHom.ker_rangeRestrict] using hh
  rw [actionHom_ker] at hk
  have hTN : (T : Subgroup G) ≤ N := sylow_le_centralizerSylowNormalizer T M V hTM hn
  apply le_antisymm
  · refine le_inf ?_ ?_
    · simpa only [Sylow.coe_subtype,map_subgroupOf_eq_of_le hTN] using
        pCoreIn_le_sylow N (T.subtype hTN)
    · rintro x ⟨n,hn',rfl⟩
      exact hk hn'
  · exact le_pCoreIn_of_normalizes (T.isPGroup'.to_le inf_le_left)
      (le_inf (inf_le_left.trans hTM) R.le_normalizer) inf_le_right
end CFSG.Quasithin.ChapterD.UniqueFactor
