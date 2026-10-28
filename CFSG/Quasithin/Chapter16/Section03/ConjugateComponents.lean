module

public import CFSG.Quasithin.Chapter16.Section03.Basic
public import CFSG.Quasithin.Chapter16.Section03.ConjugateComponents.Pumpup
public import Theory.GroupTheory.PResidual.PrimeTo

/-!
# Conjugate components and the two-element family in §16.3

Lemma 16.3.1 first uses A.1.34(2) in N_G(L): together with L, two
components of C_G(L) isomorphic to L would give three such components.
Consequently N_G(L) normalizes the unique possible component J of C_G(L).

For J = Lᵍ, A.1.34(1.i) gives O^{r′}(N_G(L)) = LJ. The center of L
is a two-group by (E1). A relative-index calculation therefore gives
O^{r′}(C_G(L)) = J. Conjugation and residual monotonicity give
O^{r′}(C_G(J)) = L and Jᵍ = L. Thus g swaps the actual family
Theta(L) = {L, J}. Its point stabilizer has index two, contradicting the
ambient Sylow subgroup T lying in that stabilizer.

The A.1.34 conclusions are explicit mathematical inputs. Its exceptional
SU₃(8) branch must be excluded by the earlier source results; the model
predicate uses an actual special-unitary isomorphism and fixed-field order 8.
Relative normality of L in C_G(z) is precisely the input from 16.2.4.
No normality of L in G is assumed. The parent section discharges these inputs.

The imported Pumpup module supplies 16.3.13(3) with its I.3.1 premise explicit.
Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
A.1.34, pp.29–30, and Lemmas 16.3.1 and 16.3.13(3), pp.1177 and 1182.
-/

@[expose] public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter16.ConjugateComponents
universe u
variable {G : Type u} [Group G] [Finite G]

/-- The component multiplicity conclusion A.1.34(2), with actual isomorphisms. -/
def ComponentMultiplicity (K : GroupClass.{u}) (G : Type u) [Group G] [Finite G] : Prop :=
  IsQuasithin G → ∀ H : Subgroup G, IsKGroup K H →
    ∀ A B D : Subgroup G, IsComponentIn A H → IsComponentIn B H → A ≠ B →
      Nonempty (A ≃* B) → IsComponentIn D H → Nonempty (D ≃* A) → D = A ∨ D = B

/-- The actual ambient conjugates of L that are ordinary components of N_G(L). -/
def theta (L : Subgroup G) : Set (Subgroup G) :=
  {J | (∃ x : G, L.map (MulAut.conj x).toMonoidHom = J) ∧
    IsComponentIn J (normalizer (L : Set G))}

omit [Finite G] in
private theorem not_le_own_centralizer {L H : Subgroup G} (hL : IsComponentIn L H) :
    ¬ L ≤ centralizer (L : Set G) := by
  intro hc
  let := hL.quasisimple
  have he : ⁅L, L⁆ = ⊥ := commutator_eq_bot_iff_le_centralizer.mpr hc
  rw [commutator_eq_self] at he
  exact hL.ne_bot he

/-- The normalizer of a component in the central setup is proper, supplying proper-K. -/
private theorem normalizer_proper {K : GroupClass.{u}} (hG : Hypothesis1611 K G)
    {T : Sylow 2 G} {z : G} {L : Subgroup G} (h : CentralComponentSetup T z L) :
    normalizer (L : Set G) ≠ ⊤ := by
  intro he
  let := hG.simple
  let : L.Normal := normalizer_eq_top_iff.mp he
  rcases (inferInstance : L.Normal).eq_bot_or_eq_top with hb | ht
  · exact (show IsComponentIn L (involutionCentralizer z) from h.component).ne_bot hb
  · apply twoLocal_ne_top_of_nonabelian_simple hG.nonabelian
      (isTwoLocal_involution_centralizer h.involution)
    exact top_unique (ht ▸ h.component.1)

/-- The first assertion of 16.3.1, conditional on A.1.34(2). -/
theorem unique_isomorphic_centralizer_component {K : GroupClass.{u}}
    (hG : Hypothesis1611 K G) {T : Sylow 2 G} {z : G} {L : Subgroup G}
    (h : CentralComponentSetup T z L) (multiplicity : ComponentMultiplicity K G)
    {A B : Subgroup G} (hA : IsComponentIn A (centralizer (L : Set G)))
    (hB : IsComponentIn B (centralizer (L : Set G)))
    (eA : Nonempty (A ≃* L)) (eB : Nonempty (B ≃* L)) : A = B := by
  have hL : IsComponentIn L (normalizer (L : Set G)) :=
    (show IsComponentIn L (involutionCentralizer z) from h.component).normalizer
  have hAN := hA.of_subnormal (centralizer_le_normalizer (L : Set G))
    (inferInstance : ((centralizer (L : Set G)).subgroupOf
      (normalizer (L : Set G))).Normal).isSubnormal
  have hBN := hB.of_subnormal (centralizer_le_normalizer (L : Set G))
    (inferInstance : ((centralizer (L : Set G)).subgroupOf
      (normalizer (L : Set G))).Normal).isSubnormal
  have hLA : L ≠ A := fun he => not_le_own_centralizer hL (he.le.trans hA.1)
  have hLB : B ≠ L := fun he => not_le_own_centralizer hL (he.ge.trans hB.1)
  have eLA : Nonempty (L ≃* A) := eA.map MulEquiv.symm
  exact ((multiplicity hG.quasithin _ (hG.properK _ (normalizer_proper hG h))
    L A B hL hAN hLA eLA hBN eB).resolve_left hLB).symm

/-- A contrary conjugate component gives exactly the displayed two members of Theta(L). -/
theorem theta_eq_pair {K : GroupClass.{u}} (hG : Hypothesis1611 K G)
    {T : Sylow 2 G} {z : G} {L : Subgroup G} (h : CentralComponentSetup T z L)
    (multiplicity : ComponentMultiplicity K G) (g : G)
    (hg : IsComponentIn (L.map (MulAut.conj g).toMonoidHom) (centralizer (L : Set G))) :
    theta L = {L, L.map (MulAut.conj g).toMonoidHom} := by
  let A := L.map (MulAut.conj g).toMonoidHom
  have hL : IsComponentIn L (normalizer (L : Set G)) :=
    (show IsComponentIn L (involutionCentralizer z) from h.component).normalizer
  have hAN := hg.of_subnormal (centralizer_le_normalizer (L : Set G))
    (inferInstance : ((centralizer (L : Set G)).subgroupOf
      (normalizer (L : Set G))).Normal).isSubnormal
  have hLA : L ≠ A := fun he => not_le_own_centralizer hL (he.le.trans hg.1)
  ext J
  constructor
  · rintro ⟨⟨x, rfl⟩, hJ⟩
    have hh := multiplicity hG.quasithin _ (hG.properK _ (normalizer_proper hG h))
      L A (L.map (MulAut.conj x).toMonoidHom) hL hAN hLA
      ⟨(MulAut.conj g).subgroupMap L⟩ hJ ⟨((MulAut.conj x).subgroupMap L).symm⟩
    simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using hh
  · rintro (rfl | rfl)
    · exact ⟨⟨1, by simp only [map_one]; change J.map (MonoidHom.id G) = J; exact map_id J⟩, hL⟩
    · exact ⟨⟨g, rfl⟩, hAN⟩

/-- Uniqueness forces N_G(L) to normalize the component isomorphic to L in C_G(L). -/
private theorem normalizer_le_normalizer_component {K : GroupClass.{u}}
    (hG : Hypothesis1611 K G) {T : Sylow 2 G} {z : G} {L J : Subgroup G}
    (h : CentralComponentSetup T z L) (multiplicity : ComponentMultiplicity K G)
    (hJ : IsComponentIn J (centralizer (L : Set G))) (eJL : Nonempty (J ≃* L)) :
    normalizer (L : Set G) ≤ normalizer (J : Set G) := by
  intro n hn
  apply mem_normalizer_iff_map_conj_eq.mpr
  have hnL : L.map (MulAut.conj n).toMonoidHom = L :=
    mem_normalizer_iff_map_conj_eq.mp hn
  have hm := hJ.map (MulAut.conj n)
  rw [map_centralizer_equiv] at hm
  change IsComponentIn (J.map (MulAut.conj n).toMonoidHom)
    (centralizer (L.map (MulAut.conj n).toMonoidHom : Set G)) at hm
  rw [hnL] at hm
  exact unique_isomorphic_centralizer_component hG h multiplicity hm hJ
    (eJL.map fun e => ((MulAut.conj n).subgroupMap J).symm.trans e) eJL

end CFSG.Quasithin.Chapter16.ConjugateComponents

open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter16.ConjugateComponents
variable {G : Type*} [Group G]

private theorem conj_map_mul (A : Subgroup G) (a b : G) :
    A.map (MulAut.conj (a * b)).toMonoidHom =
      (A.map (MulAut.conj b).toMonoidHom).map (MulAut.conj a).toMonoidHom := by
  rw [map_map]
  congr 1
  ext x
  simp [MulAut.conj_apply, mul_assoc]

private theorem conj_map_one (A : Subgroup G) :
    A.map (MulAut.conj (1 : G)).toMonoidHom = A := by
  have he : (MulAut.conj (1 : G)).toMonoidHom = MonoidHom.id G := by
    ext x
    simp
  rw [he, map_id]

/-- Setwise normalizer for the actual conjugation action on a family of subgroups. -/
private def familyNormalizer (F : Set (Subgroup G)) : Subgroup G where
  carrier := {g | ∀ A : Subgroup G, A.map (MulAut.conj g).toMonoidHom ∈ F ↔ A ∈ F}
  one_mem' := by intro A; rw [conj_map_one]
  mul_mem' := by
    intro a b ha hb A
    rw [conj_map_mul, ha, hb]
  inv_mem' := by
    intro g hg A
    have hh := hg (A.map (MulAut.conj g⁻¹).toMonoidHom)
    rw [← conj_map_mul, mul_inv_cancel, conj_map_one] at hh
    exact hh.symm

private theorem mem_familyNormalizer_pair_fix {L J : Subgroup G} {g : G}
    (hL : L.map (MulAut.conj g).toMonoidHom = L)
    (hJ : J.map (MulAut.conj g).toMonoidHom = J) :
    g ∈ familyNormalizer ({L, J} : Set (Subgroup G)) := by
  intro A
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
  constructor
  · rintro (h | h)
    · exact Or.inl ((map_injective (f := (MulAut.conj g).toMonoidHom)
        (MulAut.conj g).injective) (h.trans hL.symm))
    · exact Or.inr ((map_injective (f := (MulAut.conj g).toMonoidHom)
        (MulAut.conj g).injective) (h.trans hJ.symm))
  · rintro (rfl | rfl)
    · exact Or.inl hL
    · exact Or.inr hJ

private theorem mem_familyNormalizer_pair_swap {L J : Subgroup G} {g : G}
    (hL : L.map (MulAut.conj g).toMonoidHom = J)
    (hJ : J.map (MulAut.conj g).toMonoidHom = L) :
    g ∈ familyNormalizer ({L, J} : Set (Subgroup G)) := by
  intro A
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
  constructor
  · rintro (h | h)
    · exact Or.inr ((map_injective (f := (MulAut.conj g).toMonoidHom)
        (MulAut.conj g).injective) (h.trans hJ.symm))
    · exact Or.inl ((map_injective (f := (MulAut.conj g).toMonoidHom)
        (MulAut.conj g).injective) (h.trans hL.symm))
  · rintro (rfl | rfl)
    · exact Or.inr hL
    · exact Or.inl hJ

/-- A Sylow two-subgroup cannot fix both members of a two-element family
that an ambient element swaps. The point stabilizer would have index two. -/
private theorem no_swap_of_sylow_fixes_family [Finite G] (T : Sylow 2 G)
    {L J : Subgroup G} (F : Set (Subgroup G)) (hF : F = {L, J}) (hne : L ≠ J)
    (hTL : (T : Subgroup G) ≤ normalizer (L : Set G))
    (hTJ : (T : Subgroup G) ≤ normalizer (J : Set G))
    (g : G) (hgL : L.map (MulAut.conj g).toMonoidHom = J)
    (hgJ : J.map (MulAut.conj g).toMonoidHom = L) : False := by
  let N := familyNormalizer F
  let H := (normalizer (L : Set G)).subgroupOf N
  have hTN : (T : Subgroup G) ≤ N := by
    intro t ht
    change t ∈ familyNormalizer F
    rw [hF]
    exact mem_familyNormalizer_pair_fix
      (mem_normalizer_iff_map_conj_eq.mp (hTL ht))
      (mem_normalizer_iff_map_conj_eq.mp (hTJ ht))
  have hgN : g ∈ N := by
    change g ∈ familyNormalizer F
    rw [hF]
    exact mem_familyNormalizer_pair_swap hgL hgJ
  have hindex : H.index = 2 := by
    apply index_eq_two_iff_exists_notMem_and'.mpr
    refine ⟨⟨g, hgN⟩, ?_, ?_⟩
    · intro hmem
      exact hne ((mem_normalizer_iff_map_conj_eq.mp hmem).symm.trans hgL)
    · intro x
      have hx : L.map (MulAut.conj (x : G)).toMonoidHom = L ∨
          L.map (MulAut.conj (x : G)).toMonoidHom = J := by
        have hmem : L ∈ F := by rw [hF]; simp
        have himage := (x.property L).mpr hmem
        simpa only [hF, Set.mem_insert_iff, Set.mem_singleton_iff] using himage
      rcases hx with hx | hx
      · exact Or.inr (mem_normalizer_iff_map_conj_eq.mpr hx)
      · apply Or.inl
        change (g * (x : G)) ∈ normalizer (L : Set G)
        apply mem_normalizer_iff_map_conj_eq.mpr
        change L.map (MulAut.conj (g * (x : G))).toMonoidHom = L
        rw [conj_map_mul, hx, hgJ]
  have hTH : (T.subtype hTN : Subgroup N) ≤ H := fun x hx => hTL hx
  have hdiv := index_dvd_of_le hTH
  rw [hindex] at hdiv
  exact (T.subtype hTN).not_dvd_index hdiv

end CFSG.Quasithin.Chapter16.ConjugateComponents

open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter16.ConjugateComponents
variable {G H : Type*} [Group G] [Group H] {p : ℕ}

private theorem map_primeToResidual_le_any (f : G →* H) :
    (primeToResidual p G).map f ≤ primeToResidual p H := by
  apply le_sInf
  rintro N ⟨hN, hc⟩
  let := hN
  rw [map_le_iff_le_comap]
  apply primeToResidual_le
  rw [index_comap]
  exact hc.coprime_dvd_right (relIndex_dvd_index_of_normal N f.range)

private theorem primeToResidual_index_coprime [Finite G] [Fact p.Prime] :
    Nat.Coprime p (primeToResidual p G).index := by
  let P : Sylow p G := Classical.choice inferInstance
  have hPR : (P : Subgroup G) ≤ primeToResidual p G := by
    intro x hx
    obtain ⟨n, hn⟩ := P.isPGroup' ⟨x, hx⟩
    exact mem_primeToResidual_of_pow (congrArg Subtype.val hn)
  exact (Nat.Prime.coprime_iff_not_dvd (Fact.out : p.Prime)).mpr
    (fun hd => P.not_dvd_index (hd.trans (index_dvd_of_le hPR)))

private theorem quasisimple_primeToResidual_top [Finite G] [Fact p.Prime]
    [IsQuasisimple G] (hc : Nat.Coprime p (Nat.card (center G)))
    (hd : p ∣ Nat.card G) : primeToResidual p G = ⊤ := by
  rcases IsQuasisimple.normal_le_center_or_eq_top (primeToResidual p G) with hle | he
  · have hcop : Nat.Coprime p (Nat.card (primeToResidual p G)) :=
      hc.coprime_dvd_right (card_dvd_of_le hle)
    have hcard : Nat.Coprime p (Nat.card G) := by
      rw [← (primeToResidual p G).card_mul_index]
      exact hcop.mul_right primeToResidual_index_coprime
    exact False.elim ((Nat.Prime.coprime_iff_not_dvd (Fact.out : p.Prime)).mp hcard hd)
  · exact he

private theorem center_image (L : Subgroup G) :
    (center L).map L.subtype = L ⊓ centralizer (L : Set G) := by
  ext x
  constructor
  · rintro ⟨z, hz, rfl⟩
    refine ⟨z.property, ?_⟩
    intro k hk
    exact congrArg Subtype.val (mem_center_iff.mp hz ⟨k, hk⟩)
  · rintro ⟨hx, hc⟩
    refine ⟨⟨x, hx⟩, ?_, rfl⟩
    exact mem_center_iff.mpr fun k => Subtype.ext (hc k k.property)

private theorem residual_centralizer_of_pair [Finite G] [Fact p.Prime]
    (L J : Subgroup G) [J.Normal]
    (hJC : J ≤ centralizer (L : Set G))
    (hcenter : Nat.Coprime p (Nat.card (center L)))
    (hJ : primeToResidual p J = ⊤)
    (hres : primeToResidual p G = L ⊔ J) :
    (primeToResidual p (centralizer (L : Set G))).map
      (centralizer (L : Set G)).subtype = J := by
  let C := centralizer (L : Set G)
  have hJC' : J ≤ C := hJC
  have hinter : (L ⊔ J) ⊓ C = (L ⊓ C) ⊔ J := by
    apply le_antisymm
    · intro x hx
      obtain ⟨a, ha, b, hb, rfl⟩ := mem_sup_of_normal_right.mp hx.1
      have haC : a ∈ C := by
        simpa only [mul_inv_cancel_right] using C.mul_mem hx.2 (C.inv_mem (hJC hb))
      exact mul_mem_sup ⟨ha, haC⟩ hb
    · exact sup_le (le_inf (inf_le_left.trans le_sup_left) inf_le_right)
        (le_inf le_sup_right hJC)
  have hZ : Nat.Coprime p (Nat.card (L ⊓ C : Subgroup G)) := by
    have hcard := Nat.card_congr ((center L).equivMapOfInjective L.subtype L.subtype_injective).toEquiv
    rw [center_image] at hcard
    exact hcard ▸ hcenter
  have hR : Nat.Coprime p ((L ⊔ J).relIndex C) := by
    rw [← hres]
    exact (primeToResidual_index_coprime (G := G) (p := p)).coprime_dvd_right
      (relIndex_dvd_index_of_normal _ C)
  have hindex : Nat.Coprime p (J.relIndex C) := by
    have hmul := relIndex_inf_mul_relIndex J (L ⊔ J) C
    rw [inf_eq_left.mpr (show J ≤ L ⊔ J from le_sup_right), hinter, relIndex_sup_right] at hmul
    rw [← hmul]
    exact (hZ.coprime_dvd_right (relIndex_dvd_card J (L ⊓ C))).mul_right hR
  apply le_antisymm
  · have hle := primeToResidual_le (J.subgroupOf C) hindex
    simpa only [map_subgroupOf_eq_of_le hJC'] using map_mono (f := C.subtype) hle
  · have hle := map_primeToResidual_le_any (p := p) (inclusion hJC')
    rw [hJ] at hle
    have hm := map_mono (f := C.subtype) hle
    rw [map_map] at hm
    change (⊤ : Subgroup J).map J.subtype ≤ _ at hm
    simpa only [← MonoidHom.range_eq_map, range_subtype] using hm

end CFSG.Quasithin.Chapter16.ConjugateComponents

namespace CFSG.Quasithin.Chapter16.ConjugateComponents
open Subgroup Theory.GroupTheory
universe u
variable {G : Type u} [Group G] [Finite G]
/-- A.1.34(1.i) after excluding its SU₃(8) alternative. The prime-divisibility
clause is the consequence of the source prime dividing a two-local subgroup
of A/Z(A). Only this weaker divisibility clause is needed here. -/
def ComponentPairResidual (K : GroupClass.{u}) (G : Type u) [Group G] [Finite G] : Prop :=
  IsQuasithin G → ∀ H : Subgroup G, IsKGroup K H →
    ∀ A B : Subgroup G, IsComponentIn A H → IsComponentIn B H → A ≠ B →
      Nonempty (A ≃* B) → ¬ ChapterA.Section02.IsSpecialUnitaryModel A 3 8 →
      ∃ r : ℕ, r.Prime ∧ r ≠ 2 ∧ r ∣ Nat.card A ∧
        (primeToResidual r H).map H.subtype = A ⊔ B

private def centralizerInEquiv {N L : Subgroup G} (hLN : L ≤ N)
    (hCN : centralizer (L : Set G) ≤ N) :
    centralizer (L.subgroupOf N : Set N) ≃* centralizer (L : Set G) where
  toFun x := ⟨x.val.val, fun y hy =>
    congrArg Subtype.val (x.property ⟨y, hLN hy⟩ hy)⟩
  invFun x := ⟨⟨x, hCN x.property⟩, fun y hy => Subtype.ext (x.property y hy)⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl

private theorem centralizer_residual_in {N L J : Subgroup G} {r : ℕ} [Fact r.Prime]
    (hLN : L ≤ N) (hJN : J ≤ N) (hCN : centralizer (L : Set G) ≤ N)
    (hnJ : (J.subgroupOf N).Normal) (hJC : J ≤ centralizer (L : Set G))
    (hcenter : Nat.Coprime r (Nat.card (center L)))
    (hJ : primeToResidual r J = ⊤)
    (hres : (primeToResidual r N).map N.subtype = L ⊔ J) :
    (primeToResidual r (centralizer (L : Set G))).map
      (centralizer (L : Set G)).subtype = J := by
  let := hnJ
  have hc : Nat.Coprime r (Nat.card (center (L.subgroupOf N))) := by
    rw [Nat.card_congr (Subgroup.centerCongr (subgroupOfEquivOfLe hLN)).toEquiv]
    exact hcenter
  have hJ' : primeToResidual r (J.subgroupOf N) = ⊤ := by
    apply (map_injective (f := (subgroupOfEquivOfLe hJN).toMonoidHom)
      (subgroupOfEquivOfLe hJN).injective)
    rw [map_primeToResidual, hJ, map_top_of_surjective _ (subgroupOfEquivOfLe hJN).surjective]
  have hres' : primeToResidual r N = L.subgroupOf N ⊔ J.subgroupOf N := by
    apply (map_injective N.subtype_injective)
    rw [Subgroup.map_sup, map_subgroupOf_eq_of_le hLN, map_subgroupOf_eq_of_le hJN, hres]
  have hJC' : J.subgroupOf N ≤ centralizer (L.subgroupOf N : Set N) := by
    intro x hx y hy
    exact Subtype.ext (hJC hx y hy)
  have he := residual_centralizer_of_pair (L.subgroupOf N) (J.subgroupOf N)
    hJC' hc hJ' hres'
  let e := centralizerInEquiv hLN hCN
  calc
    (primeToResidual r (centralizer (L : Set G))).map
        (centralizer (L : Set G)).subtype =
      ((primeToResidual r (centralizer (L.subgroupOf N : Set N))).map e.toMonoidHom).map
        (centralizer (L : Set G)).subtype := by rw [map_primeToResidual]
    _ = ((primeToResidual r (centralizer (L.subgroupOf N : Set N))).map
        (centralizer (L.subgroupOf N : Set N)).subtype).map N.subtype := by
      rw [map_map, map_map]
      rfl
    _ = J := by rw [he, map_subgroupOf_eq_of_le hJN]

private theorem component_center_coprime {K : GroupClass.{u}}
    (hG : Hypothesis1611 K G) {T : Sylow 2 G} {z : G} {L : Subgroup G}
    (h : CentralComponentSetup T z L) {r : ℕ} (hr : r.Prime) (hr2 : r ≠ 2) :
    Nat.Coprime r (Nat.card (center L)) := by
  rw [hG.evenType.component_center_eq_twoCore h.involution h.component]
  obtain ⟨n, hn⟩ := (pCore_isPGroup (p := 2) (G := L)).exists_card_eq
  rw [hn]
  exact ((Nat.coprime_primes hr Nat.prime_two).mpr hr2).pow_right n

/-- Derive the centralizer residual from the normalizer residual in A.1.34.
The index argument uses the two-group center supplied by (E1). -/
theorem centralizer_residual_identity {K : GroupClass.{u}}
    (hG : Hypothesis1611 K G) {T : Sylow 2 G} {z : G} {L J : Subgroup G}
    (h : CentralComponentSetup T z L) (multiplicity : ComponentMultiplicity K G)
    (pairResidual : ComponentPairResidual K G)
    (hnotSU : ¬ ChapterA.Section02.IsSpecialUnitaryModel L 3 8)
    (hJ : IsComponentIn J (centralizer (L : Set G))) (eJL : Nonempty (J ≃* L)) :
    ∃ r : ℕ, r.Prime ∧ r ≠ 2 ∧ r ∣ Nat.card L ∧
      (primeToResidual r (normalizer (L : Set G))).map (normalizer (L : Set G)).subtype = L ⊔ J ∧
      primeToResidual r L = ⊤ ∧
      (primeToResidual r (centralizer (L : Set G))).map (centralizer (L : Set G)).subtype = J := by
  let N := normalizer (L : Set G)
  have hLN : L ≤ N := L.le_normalizer
  have hCN : centralizer (L : Set G) ≤ N := centralizer_le_normalizer _
  have hJN : J ≤ N := hJ.1.trans hCN
  have hL : IsComponentIn L N :=
    (show IsComponentIn L (involutionCentralizer z) from h.component).normalizer
  have hJNcomp := hJ.of_subnormal hCN
    (inferInstance : ((centralizer (L : Set G)).subgroupOf N).Normal).isSubnormal
  have hne : L ≠ J := fun he => not_le_own_centralizer hL (he.le.trans hJ.1)
  obtain ⟨r, hr, hr2, hrL, hres⟩ := pairResidual hG.quasithin N
    (hG.properK N (normalizer_proper hG h)) L J hL hJNcomp hne
    (eJL.map MulEquiv.symm) hnotSU
  let : Fact r.Prime := ⟨hr⟩
  have hc := component_center_coprime hG h hr hr2
  let := hL.quasisimple
  let := hJ.quasisimple
  obtain ⟨e⟩ := eJL
  have hcrJ : Nat.Coprime r (Nat.card (center J)) := by
    rw [Nat.card_congr (Subgroup.centerCongr e).toEquiv]
    exact hc
  have hrJ : r ∣ Nat.card J := by rwa [Nat.card_congr e.toEquiv]
  have hJres := quasisimple_primeToResidual_top hcrJ hrJ
  have hnJ : (J.subgroupOf N).Normal :=
    (normal_subgroupOf_iff_le_normalizer hJN).mpr
      (normalizer_le_normalizer_component hG h multiplicity hJ ⟨e⟩)
  exact ⟨r, hr, hr2, hrL, hres, quasisimple_primeToResidual_top hc hrL,
    centralizer_residual_in hLN hJN hCN hnJ hJ.1 hc hJres hres⟩

omit [Finite G] in
private theorem embedded_residual_mono {r : ℕ} {A B : Subgroup G} (hAB : A ≤ B) :
    (primeToResidual r A).map A.subtype ≤ (primeToResidual r B).map B.subtype := by
  have hle := map_mono (f := B.subtype)
    (map_primeToResidual_le_any (p := r) (inclusion hAB))
  rw [map_map] at hle
  exact hle

omit [Finite G] in
private theorem embedded_centralizer_residual_conj (r : ℕ) (L : Subgroup G) (g : G) :
    ((primeToResidual r (centralizer (L : Set G))).map (centralizer (L : Set G)).subtype).map
      (MulAut.conj g).toMonoidHom =
    (primeToResidual r (centralizer (L.map (MulAut.conj g).toMonoidHom : Set G))).map
      (centralizer (L.map (MulAut.conj g).toMonoidHom : Set G)).subtype := by
  let C := centralizer (L : Set G)
  let D := centralizer (L.map (MulAut.conj g).toMonoidHom : Set G)
  have hCD : C.map (MulAut.conj g).toMonoidHom = D := by
    change (centralizer (L : Set G)).map (MulAut.conj g).toMonoidHom =
      centralizer (L.map (MulAut.conj g).toMonoidHom : Set G)
    rw [map_centralizer_equiv]
    rfl
  let e : C ≃* D := ((MulAut.conj g).subgroupMap C).trans (MulEquiv.subgroupCongr hCD)
  have hm := congrArg (Subgroup.map D.subtype) (map_primeToResidual (p := r) e)
  rw [map_map] at hm ⊢
  exact hm

/-- The genuine contrary configuration in 16.3.1: the two-element family,
the swap, and all three prime-complement residual identities. -/
theorem conjugate_component_configuration {K : GroupClass.{u}}
    (hG : Hypothesis1611 K G) {T : Sylow 2 G} {z : G} {L : Subgroup G}
    (h : CentralComponentSetup T z L)
    (multiplicity : ComponentMultiplicity K G) (pairResidual : ComponentPairResidual K G)
    (hnotSU : ¬ ChapterA.Section02.IsSpecialUnitaryModel L 3 8) (g : G)
    (hg : IsComponentIn (L.map (MulAut.conj g).toMonoidHom) (centralizer (L : Set G))) :
    let J := L.map (MulAut.conj g).toMonoidHom
    theta L = {L, J} ∧ L ≠ J ∧
      J.map (MulAut.conj g).toMonoidHom = L ∧
      ∃ r : ℕ, r.Prime ∧ r ≠ 2 ∧ r ∣ Nat.card L ∧
        (primeToResidual r (normalizer (L : Set G))).map (normalizer (L : Set G)).subtype = L ⊔ J ∧
        (primeToResidual r (centralizer (L : Set G))).map (centralizer (L : Set G)).subtype = J ∧
        (primeToResidual r (centralizer (J : Set G))).map (centralizer (J : Set G)).subtype = L := by
  let J := L.map (MulAut.conj g).toMonoidHom
  have hL : IsComponentIn L (normalizer (L : Set G)) :=
    (show IsComponentIn L (involutionCentralizer z) from h.component).normalizer
  have hne : L ≠ J := fun he => not_le_own_centralizer hL (he.le.trans hg.1)
  have eJL : Nonempty (J ≃* L) := ⟨((MulAut.conj g).subgroupMap L).symm⟩
  obtain ⟨r, hr, hr2, hrL, hRN, hRL, hRC⟩ :=
    centralizer_residual_identity hG h multiplicity pairResidual hnotSU hg eJL
  have hback : (primeToResidual r (centralizer (J : Set G))).map
      (centralizer (J : Set G)).subtype = J.map (MulAut.conj g).toMonoidHom := by
    rw [← embedded_centralizer_residual_conj r L g, hRC]
  have hLCJ : L ≤ centralizer (J : Set G) := le_centralizer_iff.mp hg.1
  have hLJg : L ≤ J.map (MulAut.conj g).toMonoidHom := by
    have hm := embedded_residual_mono (r := r) hLCJ
    rw [hRL, ← MonoidHom.range_eq_map, range_subtype, hback] at hm
    exact hm
  have hswap : J.map (MulAut.conj g).toMonoidHom = L := by
    apply (eq_of_le_of_card_ge hLJg _).symm
    exact le_of_eq ((Nat.card_congr ((MulAut.conj g).subgroupMap J).toEquiv).symm.trans
      (Nat.card_congr ((MulAut.conj g).subgroupMap L).toEquiv).symm)
  exact ⟨theta_eq_pair hG h multiplicity g hg, hne, hswap,
    r, hr, hr2, hrL, hRN, hRC, hback.trans hswap⟩

/-- The conjugate-component exclusion of 16.3.1 in the exact signature used
by the published standardness criterion. The additional inputs are A.1.34,
the earlier SU₃(8) exclusion, and relative normality from 16.2.4. -/
theorem no_conjugate_component {K : GroupClass.{u}}
    (hG : Hypothesis1611 K G) {T : Sylow 2 G} {z : G} {L : Subgroup G}
    (h : CentralComponentSetup T z L)
    (hn : (L.subgroupOf (involutionCentralizer z)).Normal)
    (multiplicity : ComponentMultiplicity K G) (pairResidual : ComponentPairResidual K G)
    (hnotSU : ¬ ChapterA.Section02.IsSpecialUnitaryModel L 3 8) :
    ∀ g : G, ¬ IsComponentIn (L.map (MulAut.conj g).toMonoidHom) (centralizer (L : Set G)) := by
  intro g hg
  obtain ⟨hTheta, hne, hswap, _⟩ :=
    conjugate_component_configuration hG h multiplicity pairResidual hnotSU g hg
  have hTN := h.sylow_le_normalizer_of_normal hn
  exact no_swap_of_sylow_fixes_family T (theta L) hTheta hne hTN
    (hTN.trans (normalizer_le_normalizer_component hG h multiplicity hg
      ⟨((MulAut.conj g).subgroupMap L).symm⟩)) g rfl hswap

end CFSG.Quasithin.Chapter16.ConjugateComponents
