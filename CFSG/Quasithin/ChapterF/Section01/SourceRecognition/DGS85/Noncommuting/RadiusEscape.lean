module
public import Stellmacher.SectionsOneToFourDefs
public import Theory.GroupTheory.PCoreLocalSetup
public import Theory.GroupTheory.Commutator.CentralizingComplement
public import Theory.GroupTheory.SylowCommutatorCore

/-!
# The subgroup argument for DGS (7.2)

A two-subgroup V containing Z and normalizing Z, if trapped in the opposite
vertex group P, normalizes the Sylow product Z O₂(P) and therefore lies in it.
As O₂(P) centralizes the opposite center Z′, one obtains [V,Z′] = [Z,Z′].
Thus Z′ normalizes every subgroup between this commutator and V. The two
source radius cases then yield, respectively, a forbidden normal center
product or a nonzero subgroup normal in both adjacent local groups.

The final lemma lifts a Sylow product from the source local actor to the full
vertex group using its odd relative index; these groups are not identified.
`GraphRadius` applies the arguments to the actual graph subgroups.

Source: DGS, *Groups and Graphs* (1985), (7.2), printed p.127, using (7.1)(c),
(6.6) and (3.2)(c). Recognition and the long-distance exclusions are not proved here.
-/

public section
open Subgroup
namespace CFSG.Quasithin.ChapterF.Source.DGS85.Noncommuting
variable {G : Type*} [Group G]

private theorem core_normalized (P : Subgroup G) :
    P ≤ normalizer (P.pCoreIn 2 : Set G) := by
  simpa only [pCoreIn, normalizer_eq_top, ← MonoidHom.range_eq_map, range_subtype]
    using (pCore 2 P).le_normalizer_map P.subtype

/-- A trapped radius subgroup has exactly the critical commutator, which
controls normalization of every intermediate subgroup. -/
theorem source_radius_commutator
    (P Z Z' V : Subgroup G) (hp : IsPGroup 2 V)
    (hVZ : V ≤ normalizer (Z : Set G)) (hZV : Z ≤ V) (hVP : V ≤ P)
    (hZZ' : Z ≤ normalizer (Z' : Set G))
    (hQC : P.pCoreIn 2 ≤ centralizer (Z' : Set G))
    (hS : Stellmacher.IsSylowSubgroupIn (Z ⊔ P.pCoreIn 2) P) :
    V ≤ Z ⊔ P.pCoreIn 2 ∧ ⁅V,Z'⁆ = ⁅Z,Z'⁆ ∧
      ∀ K : Subgroup G, ⁅Z,Z'⁆ ≤ K → K ≤ V → Z' ≤ normalizer (K : Set G) := by
  have hVN : V ≤ normalizer ((Z ⊔ P.pCoreIn 2 : Subgroup G) : Set G) :=
    (le_inf hVZ (hVP.trans (core_normalized P))).trans
      (normalizer_inf_normalizer_le_normalizer_sup _ _)
  obtain ⟨T,hT⟩ := hS
  have hcontain : V ≤ Z ⊔ P.pCoreIn 2 :=
    le_sylow_image_of_normalizes P T hT hp hVP hVN
  have hjoin : ⁅Z ⊔ P.pCoreIn 2,Z'⁆ = ⁅Z,Z'⁆ := by
    simpa only [commutator_comm Z' _,sup_comm] using
      (commutator_eq_of_centralizing_sup (B := P.pCoreIn 2 ⊔ Z) rfl hQC hZZ').symm
  have hcomm : ⁅V,Z'⁆ = ⁅Z,Z'⁆ :=
    le_antisymm ((commutator_mono hcontain le_rfl).trans hjoin.le)
      (commutator_mono hZV le_rfl)
  refine ⟨hcontain,hcomm,?_⟩
  intro K hRK hKV
  apply le_normalizer_iff_commutator_le_left.mpr
  exact ((commutator_mono hKV le_rfl).trans hcomm.le).trans hRK

/-- The radius-one mechanism: local generation makes the adjacent center
product normal, contradicting the earlier (6.6) obstruction. -/
theorem source_radius_escape_of_product_obstruction
    (P H M Z Z' Zₗ V : Subgroup G) (hp : IsPGroup 2 V)
    (hVZ : V ≤ normalizer (Z : Set G)) (hZV : Z ≤ V)
    (hZZ' : Z ≤ normalizer (Z' : Set G))
    (hZ'Z : Z' ≤ normalizer (Z : Set G))
    (hQC : P.pCoreIn 2 ≤ centralizer (Z' : Set G))
    (hS : Stellmacher.IsSylowSubgroupIn (Z ⊔ P.pCoreIn 2) P)
    (hₗV : Zₗ ≤ V) (hgen : Z' ⊔ (H ⊓ M) = H)
    (hHZ : H ≤ normalizer (Z : Set G)) (hMZₗ : M ≤ normalizer (Zₗ : Set G))
    (hobs : ¬ H ≤ normalizer ((Zₗ ⊔ Z : Subgroup G) : Set G)) :
    ¬ V ≤ P := by
  intro hVP
  have hinterval := (source_radius_commutator P Z Z' V hp hVZ hZV hVP hZZ' hQC hS).2.2
  have hZ'K : Z' ≤ normalizer ((Zₗ ⊔ Z : Subgroup G) : Set G) :=
    hinterval _ ((le_normalizer_iff_commutator_le_left.mp hZ'Z).trans le_sup_right)
      (sup_le hₗV hZV)
  apply hobs
  rw [← hgen]
  refine sup_le hZ'K ?_
  exact (le_inf (inf_le_right.trans hMZₗ) (inf_le_left.trans hHZ)).trans
    (normalizer_inf_normalizer_le_normalizer_sup _ _)

/-- The radius-two mechanism: an adjacent radius subgroup becomes common
normal, contrary to the faithful amalgam obstruction. -/
theorem source_radius_escape_of_common_normal_obstruction
    (P H M Z Z' V Vₗ : Subgroup G) (hp : IsPGroup 2 V)
    (hVZ : V ≤ normalizer (Z : Set G)) (hZV : Z ≤ V)
    (hZZ' : Z ≤ normalizer (Z' : Set G))
    (hZ'Z : Z' ≤ normalizer (Z : Set G))
    (hQC : P.pCoreIn 2 ≤ centralizer (Z' : Set G))
    (hS : Stellmacher.IsSylowSubgroupIn (Z ⊔ P.pCoreIn 2) P)
    (hZₗ : Z ≤ Vₗ) (hₗV : Vₗ ≤ V) (hₗHM : Vₗ ≤ H ⊓ M)
    (hgen : Z' ⊔ (H ⊓ M) = H) (hMₗ : M ≤ normalizer (Vₗ : Set G))
    (hne : Z ≠ ⊥)
    (hobs : ∀ K : Subgroup G, K ≤ H ⊓ M →
      H ≤ normalizer (K : Set G) → M ≤ normalizer (K : Set G) → K = ⊥) :
    ¬ V ≤ P := by
  intro hVP
  have hinterval := (source_radius_commutator P Z Z' V hp hVZ hZV hVP hZZ' hQC hS).2.2
  have hZ'ₗ := hinterval Vₗ
    ((le_normalizer_iff_commutator_le_left.mp hZ'Z).trans hZₗ) hₗV
  have hHₗ : H ≤ normalizer (Vₗ : Set G) := by
    rw [← hgen]
    exact sup_le hZ'ₗ (inf_le_right.trans hMₗ)
  exact hne (bot_unique (hZₗ.trans (hobs Vₗ hₗHM hHₗ hMₗ).le))


/-- Transfer a literal Sylow subgroup from the local actor to the full
vertex stabilizer, retaining the actual relative index. -/
theorem sylow_in_overgroup_of_odd_relIndex (P L A : Subgroup G) [Finite P]
    (hLP : L ≤ P) (hS : Stellmacher.IsSylowSubgroupIn A L)
    (hi : ¬ 2 ∣ L.relIndex P) : Stellmacher.IsSylowSubgroupIn A P := by
  obtain ⟨T,hT⟩ := hS
  have hAL : A ≤ L := hT ▸ map_subtype_le (T : Subgroup L)
  let : Finite L := Finite.of_injective (inclusion hLP) (inclusion_injective hLP)
  have he : A.subgroupOf L = (T : Subgroup L) := by
    rw [← hT]
    exact comap_map_eq_self_of_injective L.subtype_injective _
  have hiL : ¬ 2 ∣ A.relIndex L := by
    change ¬ 2 ∣ (A.subgroupOf L).index
    rw [he]
    exact T.not_dvd_index
  have hiP : ¬ 2 ∣ (A.subgroupOf P).index := by
    change ¬ 2 ∣ A.relIndex P
    rw [← relIndex_mul_relIndex A L P hAL hLP]
    exact fun hd => (Nat.prime_two.dvd_mul.mp hd).elim hiL hi
  have hp : IsPGroup 2 A := hT ▸ T.isPGroup'.map L.subtype
  exact ⟨hp.comap_subtype.toSylow hiP, map_subgroupOf_eq_of_le (hAL.trans hLP)⟩

end CFSG.Quasithin.ChapterF.Source.DGS85.Noncommuting
