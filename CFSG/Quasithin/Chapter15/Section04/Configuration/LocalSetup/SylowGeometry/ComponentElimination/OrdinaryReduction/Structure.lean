module

public import CFSG.Quasithin.Chapter15.Section04.Configuration.LocalSetup.SylowGeometry.ComponentElimination.Models
public import CFSG.Quasithin.Chapter15.Section04.Configuration.LocalSetup.SylowGeometry.ComponentElimination.Actions
public import CFSG.Quasithin.Chapter15.Section04.Configuration.LocalSetup.TwoFactors.ActionConstruction.Prebranch

/-!
# Ordinary components in the contrary Sylow configuration

The inversion clause of full 1.1.5 makes the odd core trivial: two
nonidentity elements of the central four-group have a nonidentity product,
which both fixes and inverts that odd core. The non-characteristic-two
C-component is therefore ordinary. For a pair, the intrinsic normal closure
of either factor is the whole product; the nonordinary normal-closure
obstruction proves that both factors are ordinary.

A component in a product of two components is one of its factors. This
constructs the actual conjugation permutation, proves distinctness from
the specified moving element, and retains relative component inclusions.
No simple-model or inner-action conclusion is asserted in this module.

Source: Aschbacher–Smith, combined manuscript (1 March 2004),
1.1.5(2),(3), printed pp.501–503; proof of 15.4.20, printed p.1164.
The private Fitting transport proof follows the existing transport argument
in Chapter1/Section02/LocalComponents/Classification/CenterFrattiniSource/
IntrinsicStructure.lean.
-/

@[expose] public section

open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter15.Section04.LocalSetup.ComponentElimination
open Chapter15.Section03.Candidates.ComponentStructure
variable {G : Type*} [Group G] [Finite G]

/-- All nonidentity elements of the four-group invert the odd core by
1.1.5(2), so that odd core is trivial. All hypotheses of 1.1.5 are retained. -/
theorem oddCore_eq_bot_of_earlier115 {κ : GroupClass} (hG : IsSimpleQTKE κ G)
    (earlier : TwoFactors.Prebranch.Lemma115OneTwo κ G) {H Z : Subgroup G}
    (hcard : Nat.card Z = 4)
    (hlocal : ∀ z ∈ Z, z ≠ 1 → ∃ (P : Sylow 2 H) (M : Subgroup G),
      Chapter1.Lemma115Hypotheses H P M z) : pPrimeCore 2 H = ⊥ := by
  classical
  have hinv (z : Z) (hz : z ≠ 1) (x : H) (hx : x ∈ pPrimeCore 2 H) :
      (z : G) * (x : G) * (z : G)⁻¹ = (x : G)⁻¹ := by
    obtain ⟨P, M, h⟩ := hlocal z z.property (fun he => hz (Subtype.ext he))
    exact (earlier hG H P M z h).2 x hx
  let _ : Nontrivial Z := Finite.one_lt_card_iff_nontrivial.mp (by rw [hcard]; decide)
  obtain ⟨a, ha⟩ := exists_ne (1 : Z)
  have hpair : ({1, a⁻¹} : Set Z).ncard < (Set.univ : Set Z).ncard := by
    rw [Set.ncard_univ, hcard, Set.ncard_pair (by simpa using ha)]
    decide
  obtain ⟨b, _, hb⟩ := Set.exists_mem_notMem_of_ncard_lt_ncard hpair
  have hb1 : b ≠ 1 := by intro h; exact hb (by simp [h])
  have hba : b ≠ a⁻¹ := by intro h; exact hb (by simp [h])
  have hab : a * b ≠ 1 := fun h => hba (eq_inv_of_mul_eq_one_right h)
  apply eq_bot_iff.mpr
  intro x hx
  have hfix : ((a * b : Z) : G) * (x : G) * ((a * b : Z) : G)⁻¹ = x := by
    calc
      _ = (a : G) * ((b : G) * (x : G) * (b : G)⁻¹) * (a : G)⁻¹ := by
        change ((a : G) * (b : G)) * (x : G) * ((a : G) * (b : G))⁻¹ = _
        group
      _ = (a : G) * (x : G)⁻¹ * (a : G)⁻¹ := by rw [hinv b hb1 x hx]
      _ = ((a : G) * (x : G) * (a : G)⁻¹)⁻¹ := by group
      _ = x := by rw [hinv a ha x hx, inv_inv]
  have hxi : (x : G) = (x : G)⁻¹ := hfix.symm.trans (hinv (a * b) hab x hx)
  have hpow : x ^ 2 = 1 := Subtype.ext (by
    change (x : G) ^ 2 = 1
    rw [pow_two]
    calc
      (x : G) * (x : G) = (x : G)⁻¹ * (x : G) := congrArg (· * (x : G)) hxi
      _ = 1 := inv_mul_cancel _)
  exact orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes
    (pPrimeCore_coprime_card (p := 2) (G := H))
    (orderOf_dvd_of_pow_eq_one hpow) ((pPrimeCore 2 H).orderOf_dvd_natCard hx))

private theorem fitting_map_le {A B : Type*} [Group A] [Group B] (e : A ≃* B) :
    (fittingSubgroup A).map e.toMonoidHom ≤ fittingSubgroup B := by
  apply map_le_iff_le_comap.mpr
  apply sSup_le
  rintro N ⟨hN, hnil⟩
  apply map_le_iff_le_comap.mp
  let := hnil
  exact le_sSup ⟨hN.map _ e.surjective, Group.nilpotent_of_mulEquiv (e.subgroupMap N)⟩

private theorem fitting_map {A B : Type*} [Group A] [Group B] (e : A ≃* B) :
    (fittingSubgroup A).map e.toMonoidHom = fittingSubgroup B := by
  apply le_antisymm (fitting_map_le e)
  have h := map_mono (f := e.toMonoidHom) (fitting_map_le e.symm)
  simpa [map_map] using h

private theorem layer_map_le {A B : Type*} [Group A] [Group B] (e : A ≃* B) :
    (componentLayer A).map e.toMonoidHom ≤ componentLayer B := by
  apply map_le_iff_le_comap.mpr
  apply sSup_le
  intro L hL
  exact map_le_iff_le_comap.mp (le_sSup (hL.map_equiv e))

private theorem layer_map {A B : Type*} [Group A] [Group B] (e : A ≃* B) :
    (componentLayer A).map e.toMonoidHom = componentLayer B := by
  apply le_antisymm (layer_map_le e)
  have h := map_mono (f := e.toMonoidHom) (layer_map_le e.symm)
  simpa [map_map] using h

private theorem fstar_map {A B : Type*} [Group A] [Group B] (e : A ≃* B) :
    (generalizedFitting A).map e.toMonoidHom = generalizedFitting B := by
  rw [generalizedFitting, generalizedFitting, Subgroup.map_sup, fitting_map, layer_map]

private theorem characteristicTwo_transport {A B : Type*} [Group A] [Group B]
    (e : A ≃* B) (h : generalizedFitting A = pCore 2 A) :
    generalizedFitting B = pCore 2 B := by
  rw [← fstar_map e, h, pCore_map_iso]

/-- The ordinary branch for a single relative C-component. -/
theorem ordinary_of_cComponent {H K : Subgroup G} (hKH : K ≤ H)
    (hK : (K.subgroupOf H).IsCComponent) (hodd : pPrimeCore 2 H = ⊥)
    (hF : generalizedFitting K ≠ pCore 2 K) : IsComponent H (K.subgroupOf H) := by
  rcases cComponent_ordinary_or_characteristicTwo hK hodd with h | h
  · exact h
  · exact (hF (characteristicTwo_transport (subgroupOfEquivOfLe hKH) h)).elim

omit [Finite G] in
private theorem component_mem_pair {A B D : Subgroup G}
    (hA : IsComponent G A) (hB : IsComponent G B) (hD : IsComponent G D)
    (hDle : D ≤ A ⊔ B) : D = A ∨ D = B := by
  by_contra! hn
  have hAD := hA.commutator_eq_bot_of_ne hD hn.1.symm
  have hBD := hB.commutator_eq_bot_of_ne hD hn.2.symm
  have hc : D ≤ centralizer (D : Set G) := hDle.trans
    (sup_le (commutator_eq_bot_iff_le_centralizer.mp hAD)
      (commutator_eq_bot_iff_le_centralizer.mp hBD))
  have hh := commutator_eq_bot_iff_le_centralizer.mpr hc
  let := hD.2
  rw [commutator_eq_self] at hh
  exact (Chapter15.Section03.component_isCComponent hD).ne_bot hh

omit [Finite G] in
private theorem conjugate_mul (L : Subgroup G) (a b : G) :
    L.map (MulAut.conj (a * b)).toMonoidHom =
      (L.map (MulAut.conj b).toMonoidHom).map (MulAut.conj a).toMonoidHom := by
  rw [map_map]
  congr 1
  ext x
  simp only [MonoidHom.comp_apply, MulEquiv.toMonoidHom_eq_coe, MonoidHom.coe_coe,
    MulAut.conj_apply]
  group

omit [Finite G] in
private theorem pair_permutation {A B K : Subgroup G} [K.Normal]
    (hA : IsComponent G A) (hB : IsComponent G B) (hne : A ≠ B)
    (hprod : A ⊔ B = K) :
    ∃ π : G →* Equiv.Perm Bool, ∀ g i,
      ((if i then B else A) : Subgroup G).map (MulAut.conj g).toMonoidHom =
        if π g i then B else A := by
  classical
  let L : Bool → Subgroup G := fun i => if i then B else A
  have hinj : Function.Injective L := by
    intro i j hij
    cases i <;> cases j
    · rfl
    · exact (hne hij).elim
    · exact (hne hij.symm).elim
    · rfl
  have hL (i : Bool) : IsComponent G (L i) := by cases i <;> assumption
  have hLK (i : Bool) : L i ≤ K := by
    rw [← hprod]; cases i
    · exact le_sup_left
    · exact le_sup_right
  have hp (g : G) (i : Bool) : ∃ j, (L i).map (MulAut.conj g).toMonoidHom = L j := by
    have hle : (L i).map (MulAut.conj g).toMonoidHom ≤ A ⊔ B := by
      rw [hprod]
      exact (map_mono (hLK i)).trans_eq
        (mem_normalizer_iff_map_conj_eq.mp (show g ∈ normalizer (K : Set G) by
          rw [normalizer_eq_top]; trivial))
    rcases component_mem_pair hA hB ((hL i).map_conj g) hle with h | h
    · exact ⟨false, h⟩
    · exact ⟨true, h⟩
  choose f hf using hp
  have hf_inj (g : G) : Function.Injective (f g) := by
    intro i j hij
    apply hinj
    apply map_injective (f := (MulAut.conj g).toMonoidHom) (MulAut.conj g).injective
    rw [hf, hf, hij]
  let e (g : G) : Equiv.Perm Bool := Equiv.ofBijective (f g)
    ⟨hf_inj g, Finite.surjective_of_injective (hf_inj g)⟩
  have he (g : G) (i : Bool) : (L i).map (MulAut.conj g).toMonoidHom = L (e g i) := hf g i
  refine ⟨{ toFun := e, map_one' := ?_, map_mul' := ?_ }, he⟩
  · apply Equiv.ext
    intro i
    apply hinj
    rw [← he]
    rw [show (MulAut.conj (1 : G)).toMonoidHom = MonoidHom.id G by
      ext x; simp]
    exact map_id _
  · intro g h
    apply Equiv.ext
    intro i
    apply hinj
    change L (e (g * h) i) = L (e g (e h i))
    rw [← he (g * h) i, ← he g (e h i), conjugate_mul, he h i]

/-- The normal closure of the seed of a two-conjugate product is the
whole product; its non-characteristic-two hypothesis forces an ordinary seed. -/
theorem ordinary_seed_of_pair {H K : Subgroup G} (hKH : K ≤ H)
    (hKN : H ≤ normalizer (K : Set G)) (hodd : pPrimeCore 2 H = ⊥)
    (hF : generalizedFitting K ≠ pCore 2 K) (L : Subgroup H)
    (hL : L.IsCComponent) (r : H)
    (hprod : L ⊔ L.map (MulAut.conj r).toMonoidHom = K.subgroupOf H) :
    IsComponent H L := by
  let _ : (K.subgroupOf H).Normal := (normal_subgroupOf_iff_le_normalizer hKH).mpr hKN
  have hN : normalClosure (L : Set H) = K.subgroupOf H := by
    apply le_antisymm (normalClosure_le_normal (hprod ▸ (show L ≤ L ⊔
      L.map (MulAut.conj r).toMonoidHom from le_sup_left)))
    rw [← hprod]
    apply sup_le le_normalClosure
    rintro _ ⟨x, hx, rfl⟩
    exact (inferInstance : (normalClosure (L : Set H)).Normal).conj_mem x
      (le_normalClosure hx) r
  by_contra hn
  have hc := cComponent_normalClosure_characteristicTwo hL hn hodd
  exact hF (characteristicTwo_transport
    ((MulEquiv.subgroupCongr hN).trans (subgroupOfEquivOfLe hKH)) hc)

/-- Construct the actual two ordinary factors and their conjugation action.
The specified element of U exchanges the factors, with relative normality
used only inside H. -/
theorem ordinary_pair_of_cComponent {H K U : Subgroup G}
    (hKH : K ≤ H) (hUH : U ≤ H) (hKN : H ≤ normalizer (K : Set G))
    (hodd : pPrimeCore 2 H = ⊥) (hF : generalizedFitting K ≠ pCore 2 K)
    (L : Subgroup H) (hL : L.IsCComponent) (r : H) (hrU : (r : G) ∈ U)
    (hmove : r ∉ normalizer (L : Set H))
    (hprod : L ⊔ L.map (MulAut.conj r).toMonoidHom = K.subgroupOf H) :
    ∃ d : OrdinaryComponentPair H K U,
      d.factor false = L.map H.subtype ∧
      d.factor true = (L.map (MulAut.conj r).toMonoidHom).map H.subtype ∧
      d.action.permutation ⟨r, hrU⟩ false = true := by
  have hLo := ordinary_seed_of_pair hKH hKN hodd hF L hL r hprod
  have hRo := hLo.map_conj r
  have hne : L ≠ L.map (MulAut.conj r).toMonoidHom := by
    intro he
    exact hmove (mem_normalizer_iff_map_conj_eq.mpr he.symm)
  let _ : (K.subgroupOf H).Normal := (normal_subgroupOf_iff_le_normalizer hKH).mpr hKN
  obtain ⟨π, hπ⟩ := pair_permutation hLo hRo hne hprod
  let J : Bool → Subgroup H := fun i => if i then L.map (MulAut.conj r).toMonoidHom else L
  have hπ' (g : H) (i : Bool) : (J i).map (MulAut.conj g).toMonoidHom = J (π g i) := hπ g i
  have hJinj : Function.Injective J := by
    intro i j hij
    cases i <;> cases j
    · rfl
    · exact (hne hij).elim
    · exact (hne hij.symm).elim
    · rfl
  have hJ (i : Bool) : IsComponent H (J i) := by cases i <;> assumption
  let a : TwoFactors.MixedLocal.FactorPairAction U (fun i => (J i).map H.subtype) :=
    { distinct := fun i j hij => hJinj (map_injective H.subtype_injective hij)
      permutation := π.comp (inclusion hUH)
      conjugation := by
        intro u i
        change ((J i).map H.subtype).map (MulAut.conj (u : G)).toMonoidHom =
          (J (π (inclusion hUH u) i)).map H.subtype
        rw [← hπ' (inclusion hUH u) i]
        rw [map_map, map_map]
        congr 1 }
  refine ⟨{ factor := fun i => (J i).map H.subtype
            le_overgroup := fun i => map_subtype_le _
            component := ?_
            product := ?_
            action := a }, rfl, rfl, ?_⟩
  · intro i
    change IsComponent H (((J i).map H.subtype).comap H.subtype)
    rw [comap_map_eq_self_of_injective H.subtype_injective]
    exact hJ i
  · change L.map H.subtype ⊔ (L.map (MulAut.conj r).toMonoidHom).map H.subtype = K
    rw [← Subgroup.map_sup, hprod, map_subgroupOf_eq_of_le hKH]
  · change π r false = true
    exact hJinj (hπ' r false).symm

omit [Finite G] in
/-- Inner witnesses transport to a conjugate component when the actors commute
with the conjugating element. The witnesses are conjugated elements of the
actual component, rather than automorphisms of an unrelated model. -/
theorem centralInnerAction_conjugate {L Z : Subgroup G} (h : CentralInnerAction L Z)
    (r : G) (hr : r ∈ centralizer (Z : Set G)) :
    CentralInnerAction (L.map (MulAut.conj r).toMonoidHom) Z := by
  let e := (MulAut.conj r).subgroupMap L
  intro z
  obtain ⟨l, hl⟩ := h z
  refine ⟨e l, ?_⟩
  intro x
  obtain ⟨x, rfl⟩ := e.surjective x
  change (z : G) * (r * (x : G) * r⁻¹) * (z : G)⁻¹ =
    (r * (l : G) * r⁻¹) * (r * (x : G) * r⁻¹) * (r * (l : G) * r⁻¹)⁻¹
  have hzr : (z : G) * r = r * (z : G) := mem_centralizer_iff.mp hr z z.property
  calc
    _ = ((z : G) * r) * (x : G) * ((z : G) * r)⁻¹ := by group
    _ = (r * (z : G)) * (x : G) * (r * (z : G))⁻¹ := by rw [hzr]
    _ = r * ((z : G) * (x : G) * (z : G)⁻¹) * r⁻¹ := by group
    _ = r * ((l : G) * (x : G) * (l : G)⁻¹) * r⁻¹ := by rw [hl x]
    _ = _ := by group

end CFSG.Quasithin.Chapter15.Section04.LocalSetup.ComponentElimination
