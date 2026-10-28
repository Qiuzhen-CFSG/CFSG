module
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Components.Triangle.ZeroCoreSource.CoreSetup
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Components.Triangle.LocalGLSp4
public import CFSG.Quasithin.ChapterF.Section01.SourceDefs

/-!
# The original local pair and its full Sylow intersections

The Cartan fixes the same K₀ selected by `first_triangle_other_residual`:
it fixes L₁ and T ∩ L₁, hence both canonical residual lifts in K/O₂(K).
In that same quotient the Sylow image of L₁ is the full Sylow image of K.
Pulling back, with the entire kernel retained, gives
T ∩ K = (T ∩ L₁) O₂(K). Both factors lie in S₀ = O₂(XT).
Thus S₀ ∩ K₀ and S₀ ∩ L₂ are actual Sylow subgroups of the original locals.

These are the original normalization and Sylow inputs to genuine F.1.1;
the cross-Borel and chief-section comparisons are separate obligations.
Source: Aschbacher--Smith, combined manuscript, 1 March 2004,
11.1.2, printed p.762, from the definition of K₀ to the application of F.1.1.
-/

open Subgroup Theory.GroupTheory
open scoped MatrixGroups
open CFSG.Quasithin.ChapterA.Section03
open Matrix.PSL3.LinearThree
open CFSG.Quasithin.Chapter12.Section02
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Components.Triangle.ZeroCoreSource
@[expose] public noncomputable section
variable {G : Type*} [Group G] [Finite G]

private theorem innerSylow_eq_local_sup_core (T : Sylow 2 G) {K B : Subgroup G}
    (hK : (⊤ : Subgroup K).IsCComponent)
    (hTK : (T : Subgroup G) ≤ normalizer (K : Set G))
    (hB : B ∈ localCComponents (T : Subgroup G)) (hBK : B < K)
    (hm : ClassicalGroup.IsPSL (K ⧸ pCore 2 K) 3 4) :
    (T : Subgroup G) ⊓ K = ((T : Subgroup G) ⊓ B) ⊔ K.pCoreIn 2 := by
  obtain ⟨F,_,_,hF,⟨e⟩⟩ := hm
  let : CharP F 2 := Theory.SpecificGroups.SymplecticFour.EvenProjective.charTwo_of_card
    (show Nat.card F = 2^2 by simpa using hF)
  obtain ⟨P,hP⟩ := NormalSylowQuotientAction.intersection_sylow T K hTK
  let q := e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 K))
  have hq : Function.Surjective q := e.surjective.comp (QuotientGroup.mk'_surjective _)
  obtain ⟨g,hg⟩ := MulAction.exists_smul_eq PSL(3,F) (P.mapSurjective hq)
    (unipotentSylow F (by decide : 0 < 2) (by simpa using hF))
  let a := MulAut.conj g
  let r := a.toMonoidHom.comp q
  have hr : Function.Surjective r := a.surjective.comp hq
  have hrker : r.ker = pCore 2 K := by
    ext x
    change a (e (QuotientGroup.mk' (pCore 2 K) x)) = 1 ↔ _
    rw [a.map_eq_one_iff,e.map_eq_one_iff]
    exact QuotientGroup.eq_one_iff x
  let : Group.IsNilpotent r.ker := by rw [hrker]; exact pCore_isNilpotent
  have hrP : (P : Subgroup K).map r = unipotent F := by
    rw [←map_map]
    exact congrArg Sylow.toSubgroup hg
  have hkP : r.ker ≤ (P : Subgroup K) := by
    rw [hrker]
    exact pCore_isPGroup.le_sylow_of_normal P
  have hBP : B.subgroupOf K ∈ localCComponents (P : Subgroup K) :=
    hP.symm ▸ SourceEmbeddings.local_restrict hB hBK.le
  obtain ⟨b,hb⟩ := local_eq_rootLift hF r hr P hrP hkP hK hBP
    (fun he => hBK.not_ge (subgroupOf_eq_top.mp he))
  have hi : ((P : Subgroup K) ⊓ B.subgroupOf K).map r = unipotent F := by
    rw [hb,inf_comm,map_inf_of_ker_le r (rootLift r b) P hkP,hrP,rootLift_map hF r hr]
    exact inf_eq_right.mpr (unipotent_le_rootLocal F b)
  have he : (P : Subgroup K) = ((P : Subgroup K) ⊓ B.subgroupOf K) ⊔ pCore 2 K := by
    have hh := congrArg (comap r) (hi.trans hrP.symm)
    rw [comap_map_eq,comap_map_eq,sup_eq_left.mpr hkP,hrker] at hh
    exact hh.symm
  have hh := congrArg (map K.subtype) he
  rw [hP,Subgroup.map_sup,subgroupOf_map_subtype] at hh
  have hle : (T : Subgroup G) ⊓ B ≤ K := inf_le_right.trans hBK.le
  change (T : Subgroup G) ⊓ K =
    (((T : Subgroup G) ⊓ B).subgroupOf K).map K.subtype ⊔ K.pCoreIn 2 at hh
  rwa [map_subgroupOf_eq_of_le hle] at hh

variable {T : Sylow 2 G} {L V : Subgroup G} (D : ChosenModule T L V)
    (S : D.NonbinaryNaturalInput) {c : Coordinates D S.field} (f : InvariantFlag c)

/-- The Cartan normalizes each original flag residual. -/
theorem cartan_normalizes_flag_residual (hu : f.IsInnerUnique)
    {X : Subgroup G} (hX : IsCartan T L X) (i : Fin 2) :
    X ≤ normalizer (f.Li i : Set G) := by
  have hx : X ≤ L ⊓ normalizer (f.Vi i.castSucc : Set G) :=
    le_inf (hX.1.trans inf_le_left) (f.cartan_normalizes hu hX i.castSucc)
  exact (hx.trans (L ⊓ normalizer (f.Vi i.castSucc : Set G)).le_normalizer).trans
    (normalizer_le_normalizer_characteristic_image _ (solvableResidual _))

/-- X fixes the same second residual selected inside the original K. -/
theorem cartan_normalizes_other_residual (hu : f.IsInnerUnique)
    (hm : ClassicalGroup.IsPSL (f.Li 0 ⧸ pCore 2 (f.Li 0)) 2 (2^S.field.degree))
    {K K₀ X : Subgroup G} (hX : IsCartan T L X)
    (hK : Source.NormalComponentIn (normalizer (f.Vi 0 : Set G)) K)
    (hLK : f.Li 0 < K) (hK₀ : K₀ ∈ Chapter1.L G T) (hK₀K : K₀ < K)
    (hk : ClassicalGroup.IsPSL (K ⧸ pCore 2 K) 3 4) :
    X ≤ normalizer (K₀ : Set G) := by
  have hXN := cartan_normalizes_flag_residual D S f hu hX 0
  have hXP : X ≤ normalizer (((T : Subgroup G) ⊓ f.Li 0 : Subgroup G) : Set G) := by
    have he : (T : Subgroup G) ⊓ f.Li 0 = ((T : Subgroup G) ⊓ L) ⊓ f.Li 0 :=
      le_antisymm
        (le_inf (le_inf inf_le_left (inf_le_right.trans ((localResidual_le _).trans inf_le_left))) inf_le_right)
        (inf_le_inf inf_le_left le_rfl)
    rw [he]
    exact (le_inf (hX.1.trans cartanNormalizer_normalizes_intersection) hXN).trans
      inf_normalizer_le_normalizer_inf
  have hNK : normalizer (f.Vi 0 : Set G) ≤ normalizer (K : Set G) :=
    (normal_subgroupOf_iff_le_normalizer hK.1.1).mp hK.2
  have ht : (⊤ : Subgroup K).IsCComponent := by
    simpa only [subgroupOf_self] using hK.1.2.subgroupOf_of_le le_rfl hK.1.1
  exact (other_local_marking_of_normalizes_intersection T ht
    ((f.invariant 0).trans hNK) (flag_mem_local_of_model D S f 0 hm).1 hLK hK₀.1 hK₀K
    ((f.cartan_normalizes hu hX 0).trans hNK) hXN hXP hk).1

/-- S₀ contains the full original Sylow intersection with K, including the
kernel of K → PSL₃(4). -/
theorem component_innerSylow_le_commonTwo (hu : f.IsInnerUnique)
    (hm : ClassicalGroup.IsPSL (f.Li 0 ⧸ pCore 2 (f.Li 0)) 2 (2^S.field.degree))
    {K X : Subgroup G} (hX : IsCartan T L X)
    (hK : Source.NormalComponentIn (normalizer (f.Vi 0 : Set G)) K)
    (hLK : f.Li 0 < K) (hk : ClassicalGroup.IsPSL (K ⧸ pCore 2 K) 3 4) :
    (T : Subgroup G) ⊓ K ≤ commonTwo T X := by
  have hNK : normalizer (f.Vi 0 : Set G) ≤ normalizer (K : Set G) :=
    (normal_subgroupOf_iff_le_normalizer hK.1.1).mp hK.2
  have hTK := (f.invariant 0).trans hNK
  have ht : (⊤ : Subgroup K).IsCComponent := by
    simpa only [subgroupOf_self] using hK.1.2.subgroupOf_of_le le_rfl hK.1.1
  rw [innerSylow_eq_local_sup_core T ht hTK (flag_mem_local_of_model D S f 0 hm).1 hLK hk]
  refine sup_le ((inf_le_inf_left _ ((localResidual_le _).trans inf_le_left)).trans
    (innerSylow_le_commonTwo c hX)) ?_
  have hcT : K.pCoreIn 2 ≤ (T : Subgroup G) := by
    obtain ⟨P,hP⟩ := NormalSylowQuotientAction.intersection_sylow T K hTK
    have hh := pCoreIn_le_sylow K P
    rw [hP,subgroupOf_map_subtype] at hh
    exact hh.trans inf_le_left
  exact le_pCoreIn_of_normalizes (isPGroup_pCoreIn 2 K) (hcT.trans le_sup_right)
    ((sup_le ((f.cartan_normalizes hu hX 0).trans hNK) hTK).trans
      (normalizer_le_normalizer_characteristic_image K (pCore 2 K)))

/-- The original two local factors, with their source orientation retained. -/
def locals (K₀ L₂ : Subgroup G) (i : Fin 2) : Subgroup G := if i = 0 then K₀ else L₂

/-- The Sylow clause of genuine F.1.1 for S₀ and the original pair. -/
theorem original_pair_sylow (hu : f.IsInnerUnique)
    (hm : ClassicalGroup.IsPSL (f.Li 0 ⧸ pCore 2 (f.Li 0)) 2 (2^S.field.degree))
    {K K₀ X : Subgroup G} (hX : IsCartan T L X)
    (hK : Source.NormalComponentIn (normalizer (f.Vi 0 : Set G)) K)
    (hLK : f.Li 0 < K) (hK₀K : K₀ ≤ K)
    (hTK₀ : (T : Subgroup G) ≤ normalizer (K₀ : Set G))
    (hk : ClassicalGroup.IsPSL (K ⧸ pCore 2 K) 3 4) :
    ∀ i, ∃ P : Sylow 2 (locals K₀ (f.Li 1) i),
      (P : Subgroup (locals K₀ (f.Li 1) i)).map (locals K₀ (f.Li 1) i).subtype =
        commonTwo T X ⊓ locals K₀ (f.Li 1) i := by
  have hn (i : Fin 2) : (T : Subgroup G) ≤ normalizer (locals K₀ (f.Li 1) i : Set G) := by
    fin_cases i
    · exact hTK₀
    · exact f.sylow_normalizes_Li 1
  have hc (i : Fin 2) : (T : Subgroup G) ⊓ locals K₀ (f.Li 1) i ≤ commonTwo T X := by
    fin_cases i
    · exact (inf_le_inf_left _ hK₀K).trans (component_innerSylow_le_commonTwo D S f hu hm hX hK hLK hk)
    · exact (inf_le_inf_left _ ((localResidual_le _).trans inf_le_left)).trans
        (innerSylow_le_commonTwo c hX)
  intro i
  obtain ⟨P,hP⟩ := NormalSylowQuotientAction.intersection_sylow T _ (hn i)
  refine ⟨P,?_⟩
  rw [hP,subgroupOf_map_subtype]
  exact le_antisymm (le_inf (hc i) inf_le_right)
    (inf_le_inf_right _ (commonTwo_le_sylow X))

end
end CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Components.Triangle.ZeroCoreSource
