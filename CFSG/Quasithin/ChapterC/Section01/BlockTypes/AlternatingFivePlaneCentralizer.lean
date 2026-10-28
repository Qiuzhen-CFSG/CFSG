module

public import CFSG.Quasithin.ChapterC.Section01.BlockTypes.AlternatingFiveSylowFixed
public import CFSG.Quasithin.ChapterC.Section01.BlockStructure.Commutation.CubicSetup
public import Theory.GroupTheory.FixedSupplementCentralizer
public import Theory.SpecificGroups.Alternating.FiveSylowMaximal
public import Theory.GroupTheory.PCoreQuotientBorelNormalizer

/-!
# Borel centralizers of Sylow-fixed subgroups in an A₅ block

The ambient two-core splits over the genuine block module and the block
centralizer. The Sylow normalizer fixes the module's fixed line, hence fixes
all core elements fixed by that Sylow subgroup. Every proper block subgroup
containing this centralizer is the inverse image of an A₅ point stabilizer
under the quotient map supplied by the original linear block model.

Source: Aschbacher–Smith C.1.13(c), printed pp.124–125, and the A₅
centralizer calculation in 15.2.23, printed p.1115. The block may be
subnormal; ambient normality is not required.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterC
variable {G : Type*} [Group G] [Finite G]

/-- A Sylow normalizer fixes the whole Sylow-fixed part of the ambient core. -/
theorem IsAlternatingBlock.sylowNormalizer_centralizes_core_fixed (X : Subgroup G) (hX : IsBlock X)
    (hb : IsAlternatingBlock X 5) (P : Sylow 2 X) :
    (normalizer (P : Set X)).map X.subtype ≤
      centralizer ((pCore 2 G ⊓ centralizer ((P : Subgroup X).map X.subtype : Set G) :
        Subgroup G) : Set G) := by
  let U := (blockU X).map X.subtype
  let C := pCore 2 G ⊓ centralizer (X : Set G)
  let R := (P : Subgroup X).map X.subtype
  let B := (normalizer (P : Set X)).map X.subtype
  have hUQ : U ≤ pCore 2 G :=
    (map_mono blockU_le_core).trans (pCoreIn_le_of_subnormal 2 hX.subnormal)
  have hsplit : pCore 2 G = U ⊔ C :=
    hb.two_subgroup_eq_module_sup_centralizer pCore_isPGroup le_normalizer_of_normal
      hUQ (by rw [commutator_comm, hX.ambient_core_commutator]; exact map_mono blockU_le_core)
  have hCX : C ≤ centralizer (X : Set G) := inf_le_right
  have hCU : C ≤ centralizer (U : Set G) := hCX.trans (centralizer_le (map_subtype_le _))
  have hCR : C ≤ centralizer (R : Set G) := hCX.trans (centralizer_le (map_subtype_le _))
  have hBC : B ≤ centralizer (C : Set G) :=
    (map_subtype_le _).trans (le_centralizer_iff.mp hCX)
  let E := blockU X ⊓ centralizer (P : Set X)
  have hNE : normalizer (P : Set X) ≤ normalizer (E : Set X) :=
    (le_inf (le_top.trans ((blockU X).normalizer_eq_top.symm.le))
      (normalizer_le_normalizer_centralizer (P : Subgroup X))).trans
      inf_normalizer_le_normalizer_inf
  have hCE : normalizer (P : Set X) ≤ centralizer (E : Set X) := by
    by_cases he : E = ⊥
    · rw [he]
      intro b hb z hz
      have hz1 : z = 1 := hz
      simp only [hz1, mul_one, one_mul]
    · have hsmall := hb.sylow_fixed_card_le_two P
      have hpos := E.one_lt_card_iff_ne_bot.mpr he
      exact hNE.trans (normalizer_le_centralizer_of_card_two E (by change Nat.card E ≤ 2 at hsmall; omega))
  have hBF : B ≤ centralizer ((U ⊓ centralizer (R : Set G) : Subgroup G) : Set G) := by
    rintro b ⟨b,hb,rfl⟩ u ⟨⟨u,hu,rfl⟩,huf⟩
    have huE : u ∈ E := ⟨hu,by
      intro p hp
      exact Subtype.ext (huf p (mem_map_of_mem X.subtype hp))⟩
    exact congrArg X.subtype (hCE hb u huE)
  apply le_centralizer_iff.mpr
  rw [hsplit, sup_comm U C, inf_centralizer_sup_of_centralizing C U R
    (hCU.trans (Subgroup.centralizer_le_normalizer _)) hCR]
  exact sup_le (le_centralizer_iff.mp hBC) (le_centralizer_iff.mp hBF)

/-- A proper overgroup of the Borel has the actual point-stabilizer marking. -/
theorem IsAlternatingBlock.borel_marking_of_proper_overgroup {X : Type*} [Group X] [Finite X]
    (hb : IsAlternatingBlock X 5) (P : Sylow 2 X)
    (A : Subgroup X) (hPA : (P : Subgroup X) ≤ A) (hA : A ≠ ⊤)
    (hNA : normalizer (P : Set X) ≤ A) :
    A = normalizer (P : Set X) ∧
      ∃ e : (X ⧸ pCore 2 X) ≃* alternatingGroup (Fin 5),
        ∃ i : Fin 5, A = (MulAction.stabilizer (alternatingGroup (Fin 5)) i).comap
          (e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 X))) := by
  obtain ⟨e⟩ := hb.2.2.quotient_iso
  let q := e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 X))
  have hq : Function.Surjective q := e.surjective.comp (QuotientGroup.mk'_surjective _)
  have hk : q.ker = pCore 2 X := by
    rw [MonoidHom.ker_comp_of_injective _ _ e.injective, QuotientGroup.ker_mk']
  have hker : q.ker ≤ (P : Subgroup X) := hk ▸ pCore_isPGroup.le_sylow_of_normal P
  have hn : (normalizer (P.map q : Set (alternatingGroup (Fin 5)))).comap q =
      normalizer (P : Set X) := comap_sylow_normalizer_of_ker_le P q hq hker
  have ha : A.map q ≠ ⊤ := by
    intro he
    apply hA
    have hh := congrArg (comap q) he
    simpa only [comap_map_eq, sup_eq_left.mpr (hker.trans hPA), comap_top] using hh
  have hle := Theory.SpecificGroups.Alternating.FiveSylowMaximal.overgroup_le_sylow_normalizer
    (P.mapSurjective hq) (A.map q) (map_mono hPA) ha
  have hAN : A ≤ normalizer (P : Set X) := by
    rw [← hn]
    exact (map_le_iff_le_comap).mp hle
  have heq := le_antisymm hAN hNA
  obtain ⟨i, hi⟩ := Theory.SpecificGroups.Alternating.FiveBorelOvergroups.sylow_normalizer_eq_stabilizer
    (P.mapSurjective hq)
  refine ⟨heq,e,i,?_⟩
  rw [heq, ← hn]
  exact congrArg (comap q) hi

/-- The actual centralizer of a Sylow-fixed core subgroup is a Borel whenever
it lies in a proper block subgroup; that proper subgroup is the same Borel. -/
theorem IsAlternatingBlock.centralizer_borel_of_sylow_fixed
    (X : Subgroup G) (hX : IsBlock X) (hb : IsAlternatingBlock X 5)
    (P : Sylow 2 X) (W : Subgroup G) (hWQ : W ≤ pCore 2 G)
    (hWP : W ≤ centralizer ((P : Subgroup X).map X.subtype : Set G))
    (J : Subgroup X) (hJ : J ≠ ⊤)
    (hCJ : (centralizer (W : Set G)).comap X.subtype ≤ J) :
    (centralizer (W : Set G)).comap X.subtype = J ∧
      J = normalizer (P : Set X) ∧
      ∃ e : (X ⧸ pCore 2 X) ≃* alternatingGroup (Fin 5),
        ∃ i : Fin 5, J = (MulAction.stabilizer (alternatingGroup (Fin 5)) i).comap
          (e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 X))) := by
  have hNC : normalizer (P : Set X) ≤ (centralizer (W : Set G)).comap X.subtype := by
    apply map_le_iff_le_comap.mp
    exact (hb.sylowNormalizer_centralizes_core_fixed X hX P).trans
      (centralizer_le (le_inf hWQ hWP))
  have hPJ : (P : Subgroup X) ≤ J :=
    P.toSubgroup.le_normalizer.trans (hNC.trans hCJ)
  obtain ⟨hJN, hm⟩ := hb.borel_marking_of_proper_overgroup P J hPJ hJ (hNC.trans hCJ)
  exact ⟨le_antisymm hCJ (hJN ▸ hNC), hJN, hm⟩

end CFSG.Quasithin.ChapterC
