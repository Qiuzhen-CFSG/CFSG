module
public import CFSG.Quasithin.ChapterE.Section02.Structure.PairedMaximal
public import CFSG.Quasithin.ChapterE.Section02.Structure.ComponentModels.OriginalImage
public import Theory.GroupTheory.DisjointCommutingProduct
public import Theory.GroupTheory.InvertingHallNormalizerEscape
public import Theory.GroupTheory.Hall.TwoClosedNormal
public import CFSG.Quasithin.ChapterE.Section06.FixedPointBounds.ParabolicCartan.NormalizerEscape.ExchangedModels
public import CFSG.Quasithin.ChapterE.Section06.FixedPointBounds.ParabolicCartan.MarkedModels.Source.StarCoordinates
import all CFSG.Quasithin.ChapterB.Section06To07.Structure
/-!
# Full-Hall normalizer escape in the exchanged rank-one source row

The simple component in the original core quotient has at most two Sylow
conjugates. Its full marked Borel admits inversion of its odd supplement.
For two components, self-normalization of the Borel intersection identifies
the full intersection with the product Borel. Simultaneous inversion then
normalizes every prescribed odd-primary subgroup, including diagonal ones.
The coprime two-kernel normalizer formula lifts escape for the same subgroup
to the original carrier. Maximality yields the original generation conclusion.

Source: Aschbacher–Smith, E.2.2(1a) and 4.4.13(1), printed pp.215–216,623–624.
The genuine strong-quasithin hypothesis is retained on the source quotient;
no assumption of normality of the original component is introduced.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterE.Section06.FixedPointBounds.ParabolicCartan.NormalizerEscape
variable {G : Type*} [Group G]

private theorem commuting_pair_overlap (M K D : Subgroup G)
    (hcomm : K ≤ centralizer (D : Set G))
    (hself : K ⊓ normalizer ((K ⊓ M : Subgroup G) : Set G) = K ⊓ M)
    (e : K × D ≃* (K ⊔ D : Subgroup G))
    (he : ∀ k d, (e (k,d) : G) = (k:G)*(d:G)) :
    (M.subgroupOf (K ⊔ D)).comap e.toMonoidHom =
      (M.subgroupOf K).prod (M.subgroupOf D) := by
  ext ⟨k,d⟩
  change (e (k,d) : G) ∈ M ↔ (k:G) ∈ M ∧ (d:G) ∈ M
  rw [he]
  constructor
  · intro hx
    have hdK : (d:G) ∈ centralizer (K : Set G) := by
      intro a ha
      exact (hcomm ha d d.property).symm
    have hdA : (d:G) ∈ normalizer ((K ⊓ M : Subgroup G) : Set G) :=
      (Subgroup.centralizer_le_normalizer _) (fun a ha => hdK a ha.1)
    have hrA : (k:G)*(d:G) ∈ normalizer ((K ⊓ M : Subgroup G) : Set G) := by
      apply inf_normalizer_le_normalizer_inf
      exact ⟨(normalizer (K:Set G)).mul_mem (K.le_normalizer k.property)
        (Subgroup.centralizer_le_normalizer _ hdK),M.le_normalizer hx⟩
    have hkA : (k:G) ∈ normalizer ((K ⊓ M : Subgroup G) : Set G) := by
      simpa only [mul_inv_cancel_right] using
        (normalizer ((K ⊓ M : Subgroup G):Set G)).mul_mem hrA
          ((normalizer ((K ⊓ M : Subgroup G):Set G)).inv_mem hdA)
    have hkM : (k:G) ∈ M := (show (k:G) ∈ K ⊓ M from hself ▸ ⟨k.property,hkA⟩).2
    exact ⟨hkM, by simpa only [inv_mul_cancel_left] using M.mul_mem (M.inv_mem hkM) hx⟩
  · rintro ⟨hk,hd⟩
    exact M.mul_mem hk hd

private theorem conjugate_pair_overlap (M K : Subgroup G) (t : G) (ht : t ∈ M)
    (hcomm : K ≤ centralizer (K.map (MulAut.conj t).toMonoidHom : Set G))
    (hself : K ⊓ normalizer ((K ⊓ M : Subgroup G) : Set G) = K ⊓ M)
    (e : K × (K.map (MulAut.conj t).toMonoidHom) ≃*
      (K ⊔ K.map (MulAut.conj t).toMonoidHom : Subgroup G))
    (he : ∀ k d, (e (k,d) : G) = (k:G)*(d:G)) :
    ∃ b : K × K ≃* (K ⊔ K.map (MulAut.conj t).toMonoidHom : Subgroup G),
      (M.subgroupOf (K ⊔ K.map (MulAut.conj t).toMonoidHom)).comap b.toMonoidHom =
        (M.subgroupOf K).prod (M.subgroupOf K) := by
  let c := (MulAut.conj t).subgroupMap K
  let b := (MulEquiv.prodCongr (MulEquiv.refl K) c).trans e
  refine ⟨b,?_⟩
  have hh := commuting_pair_overlap M K _ hcomm hself e he
  ext ⟨k,l⟩
  change (e (k,c l) : G) ∈ M ↔ (k:G) ∈ M ∧ (l:G) ∈ M
  have hi := congrArg (fun A : Subgroup (K × K.map (MulAut.conj t).toMonoidHom) =>
    (k,c l) ∈ A) hh
  change ((e (k,c l) : G) ∈ M) = ((k:G) ∈ M ∧ (c l:G) ∈ M) at hi
  rw [hi]
  exact and_congr_right fun _ => (M.le_normalizer ht (l:G)).symm

private theorem escape_from_subgroup (M R A : Subgroup G) (hAR : A ≤ R)
    (hout : ¬ normalizer (A.subgroupOf R : Set R) ≤ M.subgroupOf R) :
    ¬ normalizer (A : Set G) ≤ M := by
  intro hn
  apply hout
  intro a ha
  have hh := (A.subgroupOf R).le_normalizer_map R.subtype
    (mem_map_of_mem R.subtype ha)
  rw [map_subgroupOf_eq_of_le hAR] at hh
  exact hn hh

private theorem escape_through_equiv {H : Type*} [Group H]
    (e : H ≃* G) (M A : Subgroup G)
    (hout : ¬ normalizer (A.map e.symm.toMonoidHom : Set H) ≤ M.comap e.toMonoidHom) :
    ¬ normalizer (A : Set G) ≤ M := by
  intro hn
  apply hout
  intro a ha
  have hh := (A.map e.symm.toMonoidHom).le_normalizer_map e.toMonoidHom
    (mem_map_of_mem e.toMonoidHom ha)
  simp only [map_map,MulEquiv.toMonoidHom_eq_coe,
    MulEquiv.coe_monoidHom_comp_coe_monoidHom_symm,map_id] at hh
  exact hn hh

variable [Finite G]
/-- In a strongly quasithin minimal parabolic with trivial core, the
rank-one Borel inversion data give escape for every odd-primary subgroup. -/
theorem rankOne_pair_escape
    (hG : IsStronglyQuasithin G) (S : Sylow 2 G)
    (hP : ChapterB.IsMinimalParabolicOver S ⊤)
    (hJ : ChapterB.minimalParabolicCore S hP = ⊥)
    (K : Subgroup G) (hK : IsComponent G K) [IsSimpleGroup K]
    (hgen : K ⊔ (S : Subgroup G) = ⊤)
    (hm : HasInvertingSupplement ((ChapterB.minimalParabolicMax S hP).subgroupOf K))
    {p : ℕ} [Fact p.Prime] (hp : Odd p) (A : Subgroup G)
    (hA : IsPGroup p A) (hAM : A ≤ ChapterB.minimalParabolicMax S hP) :
    ¬ normalizer (A : Set G) ≤ ChapterB.minimalParabolicMax S hP := by
  let M := ChapterB.minimalParabolicMax S hP
  have hAR : A ≤ pResidual 2 G := by
    intro a ha
    apply mem_pResidual_of_orderOf_coprime
    simpa only [Subgroup.orderOf_mk] using
      (hA.orderOf_coprime hp.coprime_two_right (⟨a,ha⟩ : A)).symm
  rcases Structure.component_normal_or_pair hG S hK hgen with hn | ⟨t,hne,hD,hcomm,hN,hR,hswap,hi⟩
  · have hAK : A ≤ K := hn.2 ▸ hAR
    exact escape_from_subgroup M K A hAK
      (hm.normalizer_not_le hp (A.subgroupOf K) hA.comap_subtype (fun _ ha => hAM ha))
  · have hs : ¬ Group.IsSolvable G := by
      intro hh
      let := hh
      let := hK.2
      exact Group.IsPerfect.not_isSolvable K inferInstance
    have hrad : solvableRadical G = ⊥ :=
      (ChapterB.minimalParabolic_nonsolvable_core_eq_radical S hP hs).symm.trans hJ
    let D := K.map (MulAut.conj (t:G)).toMonoidHom
    let R := K ⊔ D
    obtain ⟨e,he⟩ := hK.isCComponent.exists_mulEquiv_prod_sup_of_solvableRadical_eq_bot hrad hcomm
    obtain ⟨b,hb⟩ := conjugate_pair_overlap M K t
      ((ChapterB.minimalParabolicMax_spec S hP).2 t.property)
      (commutator_eq_bot_iff_le_centralizer.mp hcomm)
      (Structure.component_maximal_intersection_self_normalizing hG S hP hK hgen) e he
    have hAR' : A ≤ R := by
      change A ≤ K ⊔ K.map (MulAut.conj (t:G)).toMonoidHom
      rw [← hR]
      exact hAR
    apply escape_from_subgroup M R A hAR'
    apply escape_through_equiv b (M.subgroupOf R) (A.subgroupOf R)
    rw [hb]
    apply hm.normalizer_not_le_prod hm hp _ (hA.comap_subtype.map b.symm.toMonoidHom)
    rintro _ ⟨a,ha,rfl⟩
    rw [← hb]
    change (b (b.symm a) : G) ∈ M
    rw [MulEquiv.apply_symm_apply]
    exact hAM ha

open MarkedModels ChapterB
/-- The original exchanged rank-one source row: simultaneous full-torus
inversion preserves every prescribed odd-primary subgroup of the maximal. -/
theorem exchanged_original_escape_all_odd
    (S : Sylow 2 G) (hP : IsMinimalParabolicOver S ⊤) (K : Subgroup G)
    (hK : K.IsCComponent)
    (hc : ExchangedClauses (minimalParabolicMax S hP) K S) {f : ℕ}
    (hm : MarkedModels.ExchangedModel (minimalParabolicMax S hP) K f)
    (hgen : (⊤ : Subgroup G) = K ⊔ (S : Subgroup G))
    (hquot : IsStronglyQuasithin (G ⧸ sourceKernel (minimalParabolicMax S hP)))
    {p : ℕ} [Fact p.Prime] (hp : Odd p)
    (A : Subgroup G) (hA : IsPGroup p A) (hAM : A ≤ minimalParabolicMax S hP) :
    ¬ normalizer (A : Set G) ≤ minimalParabolicMax S hP := by
  let M := minimalParabolicMax S hP
  let J := sourceKernel M
  let q := QuotientGroup.mk' J
  let T := S.mapSurjective (QuotientGroup.mk'_surjective J)
  have hs : ¬ Group.IsSolvable G := by
    intro hh
    let := hh
    exact hK.not_isSolvable inferInstance
  have hi := Structure.source_component_simple_image S hP hs K hK hgen.symm
  let : IsSimpleGroup (sourceImage M K) := hi.1
  have hmin := (Structure.source_star_minimal_core_free S hP).1
  have hmax : minimalParabolicMax T hmin = M.map q :=
    (minimalParabolicMax_map_core S hP q (QuotientGroup.mk'_surjective J)
      (by rw [QuotientGroup.ker_mk']; exact le_rfl)).symm
  have hmod := ExchangedModel.inverting_supplement hm
  rw [source_overlap_coordinate] at hmod
  change HasInvertingSupplement ((M.map q).subgroupOf (sourceImage M K)) at hmod
  rw [← hmax] at hmod
  have hesc := rankOne_pair_escape hquot T hmin
    (Structure.source_star_minimal_core_free S hP).2 (sourceImage M K)
    hi.2.1 hi.2.2.2 hmod hp (A.map q) (hA.map q)
    (by rw [hmax]; exact map_mono hAM)
  rw [hmax] at hesc
  have hk : IsPGroup 2 q.ker := by
    rw [QuotientGroup.ker_mk']
    change IsPGroup 2 (sourceKernel M)
    rw [hc.kernel_eq]
    exact pCore_isPGroup
  exact Theory.GroupTheory.normalizer_not_le_of_two_kernel q
    (QuotientGroup.mk'_surjective J) hk M A hp hA hesc

/-- The literal generation conclusion for the prescribed odd-primary
subgroup in the exchanged source row of 4.4.13(1). -/
theorem exchanged_original_generation_all_odd
    (S : Sylow 2 G) (hP : IsMinimalParabolicOver S ⊤) (K : Subgroup G)
    (hK : K.IsCComponent)
    (hc : ExchangedClauses (minimalParabolicMax S hP) K S) {f : ℕ}
    (hm : MarkedModels.ExchangedModel (minimalParabolicMax S hP) K f)
    (hgen : (⊤ : Subgroup G) = K ⊔ (S : Subgroup G))
    (hquot : IsStronglyQuasithin (G ⧸ sourceKernel (minimalParabolicMax S hP)))
    {p : ℕ} [Fact p.Prime] (hp : Odd p)
    (A : Subgroup G) (hA : IsPGroup p A) (hAM : A ≤ minimalParabolicMax S hP) :
    minimalParabolicMax S hP ⊔ normalizer (A : Set G) = ⊤ := by
  have hout := exchanged_original_escape_all_odd S hP K hK hc hm hgen hquot hp A hA hAM
  apply (minimalParabolicMax_spec S hP).1.lt_iff.mp
  apply lt_of_le_of_ne le_sup_left
  exact fun he => hout (sup_eq_left.mp he.symm)

/-- The full-Hall formulation of the original 4.4.13(1) conclusion in the
exchanged row, including the trivial elementary subgroup. -/
theorem exchanged_original_generation
    (S : Sylow 2 G) (hP : IsMinimalParabolicOver S ⊤) (K : Subgroup G)
    (hK : K.IsCComponent)
    (hc : ExchangedClauses (minimalParabolicMax S hP) K S) {f : ℕ}
    (hm : MarkedModels.ExchangedModel (minimalParabolicMax S hP) K f)
    (hgen : (⊤ : Subgroup G) = K ⊔ (S : Subgroup G))
    (hquot : IsStronglyQuasithin (G ⧸ sourceKernel (minimalParabolicMax S hP)))
    (Y : Subgroup G) (hYM : Y ≤ minimalParabolicMax S hP)
    (hHall : IsHallSubgroup oddPrimes (Y.subgroupOf (minimalParabolicMax S hP)))
    (p : ℕ) (hp : p.Prime) (A : Subgroup G) (hA : IsElementaryAbelian p A)
    (hAY : A ≤ Y) :
    minimalParabolicMax S hP ⊔ normalizer (A : Set G) = ⊤ := by
  by_cases hbot : A = ⊥
  · rw [hbot,normalizer_eq_top,sup_top_eq]
  let : Fact p.Prime := ⟨hp⟩
  let : IsElementaryAbelian p A := hA
  have hAp : IsPGroup p A := IsElementaryAbelian.isPGroup p A
  have hYodd : Odd (Nat.card Y) := by
    have ho := OddHall.odd_hall_odd hHall
    rwa [Nat.card_congr (subgroupOfEquivOfLe hYM).toEquiv] at ho
  have hAodd : Odd (Nat.card A) := hYodd.of_dvd_nat (card_dvd_of_le hAY)
  have hpodd : Odd p := hAodd.of_dvd_nat
    (hAp.card_eq_or_dvd.resolve_left (fun hh => hbot (eq_bot_of_card_eq A hh)))
  exact exchanged_original_generation_all_odd S hP K hK hc hm hgen hquot
    hpodd A hAp (hAY.trans hYM)

end CFSG.Quasithin.ChapterE.Section06.FixedPointBounds.ParabolicCartan.NormalizerEscape
