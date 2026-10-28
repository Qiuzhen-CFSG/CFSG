module
public import CFSG.Quasithin.ChapterB.Section05.Quasisimple.SourceImplication.IrreducibleBranch.LocalClassification
public import CFSG.Quasithin.ChapterB.Section02.OffenderFactorization
public import Theory.Representation.BinaryOffender.GeneratedCore
public import Theory.GroupTheory.ElementaryThompsonQuotientNormalizer

/-!
# The rank-one B.5 row forces the actual Thompson image to be Sylow

At quadratic ratio one, each original best offender remains best on the
moved central section. The rank-one row identifies it with a full Sylow
subgroup of the component. B.2.7 supplies these offenders as the nonzero
images of the maximum elementary subgroups of R. Their images all lie in
one two-subgroup, hence coincide with the same Sylow subgroup; their join
is precisely the literal image of J(R).

Source: Aschbacher–Smith C.2.7(3)(a)(i), proof on printed p.146.
-/

public section
open Subgroup Stellmacher Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.ChapterC
open ChapterB.QuasisimpleSource
variable {G H W : Type*} [Group G] [Finite G] [Group H] [Finite H]
  [AddCommGroup W] [Module (ZMod 2) W] [FiniteDimensional (ZMod 2) W]

theorem bestOffender_sylow_of_ratio_one_row
    (ρ : Representation (ZMod 2) H W) (C : Subgroup H)
    (hCJ : C ≤ offenderSubgroup ρ)
    (s : MovedSection (ρ.comp (offenderSubgroup ρ).subtype)
      (C.subgroupOf (offenderSubgroup ρ)))
    (hratio : quadraticRatio s.action = 1)
    (hoff : ∀ B, IsBestOffender s.action B →
      ∃ S : Sylow 2 (C.subgroupOf (offenderSubgroup ρ)),
        B = (S : Subgroup _).map (C.subgroupOf (offenderSubgroup ρ)).subtype)
    {A : Subgroup H} (hA : IsBestOffender ρ A) :
    ∃ S : Sylow 2 C, A = (S : Subgroup C).map C.subtype := by
  have hAJ := hA.le_offenderSubgroup ρ
  have hA' := hA.subgroupOf ρ hAJ
  have hAm := IrreducibleBranch.moved_offender s (hA'.isOffender _)
  obtain ⟨S,hS⟩ := hoff _ (hAm.best_and_codim_eq_of_quadraticRatio_eq_one _ hratio).1
  let e : (C.subgroupOf (offenderSubgroup ρ)) ≃* C := subgroupOfEquivOfLe hCJ
  refine ⟨S.mapSurjective (f := e.toMonoidHom) e.surjective, ?_⟩
  have he := congrArg (map (offenderSubgroup ρ).subtype) hS
  rw [map_subgroupOf_eq_of_le hAJ, map_map] at he
  rw [he]
  change _ = ((S : Subgroup _).map e.toMonoidHom).map C.subtype
  rw [map_map]
  rfl

theorem thompson_image_sylow_of_bestOffenders
    (V R : Subgroup G) [V.Normal] [IsElementaryAbelian 2 V]
    (hR : IsPGroup 2 R) (hVR : V ≤ R)
    (q : G →* H) (hq : Function.Surjective q)
    (hker : q.ker = centralizer (V : Set G))
    (hnoncentral : ¬ elementaryAbelianMaxJ R ≤ q.ker)
    (C : Subgroup H)
    (hoff : ∀ A, IsBestOffender (NormalElementaryQuotient.representation V q hq hker) A →
      ∃ S : Sylow 2 C, A = (S : Subgroup C).map C.subtype) :
    ∃ S : Sylow 2 C, (S : Subgroup C).map C.subtype = (elementaryAbelianMaxJ R).map q := by
  have hmax := (ChapterB.lemma_B_2_7_local V q hq hker R hVR hnoncentral).2
  have hmem (A : Subgroup G) (hA : A ∈ elementaryAbelianMaxSubgroups R)
      (hne : A.map q ≠ ⊥) := hmax _ ⟨A,hA,rfl,hne⟩
  have hex : ∃ A ∈ elementaryAbelianMaxSubgroups R, A.map q ≠ ⊥ := by
    by_contra! hall
    apply hnoncentral
    exact sSup_le fun A hA => (map_eq_bot_iff A).mp (hall A hA)
  obtain ⟨A,hA,hAne⟩ := hex
  obtain ⟨S,hS⟩ := hoff _ (hmem A hA hAne)
  have hSle : (S : Subgroup C).map C.subtype ≤ R.map q :=
    hS ▸ map_mono hA.1
  have hSI : (S : Subgroup C) ≤ (R.map q).subgroupOf C := map_le_iff_le_comap.mp hSle
  have heq : (R.map q).subgroupOf C = (S : Subgroup C) :=
    S.is_maximal' ((hR.map q).comap_subtype) hSI
  refine ⟨S,le_antisymm ?_ ?_⟩
  · rw [←hS]
    exact map_mono (le_sSup hA)
  · apply map_le_iff_le_comap.mpr
    apply sSup_le
    intro B hB
    apply map_le_iff_le_comap.mp
    by_cases hB0 : B.map q = ⊥
    · rw [hB0]; exact bot_le
    obtain ⟨Q,hQ⟩ := hoff _ (hmem B hB hB0)
    have hBC : B.map q ≤ C := hQ ▸ map_subtype_le _
    intro b hb
    have hbS : (⟨b,hBC hb⟩ : C) ∈ (S : Subgroup C) :=
      heq ▸ (show (⟨b,hBC hb⟩ : C) ∈ (R.map q).subgroupOf C from map_mono hB.1 hb)
    exact mem_map.mpr ⟨⟨b,hBC hb⟩,hbS,rfl⟩

end CFSG.Quasithin.ChapterC
