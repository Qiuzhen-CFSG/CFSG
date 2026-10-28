module

public import Stellmacher.Recognition.Parrott.SecondNormalizer
public import Mathlib.GroupTheory.Nilpotent

/-!
# The centralizer of the supplied core involution

For the chosen involution a, its centralizer in H=C_G(z) lies in the
supplied Sylow T: centralizing a stabilizes its coset modulo J′, hence
normalizes the fixed join F. Thus S=C_H(a)=C_T(a) is a two-group.
Both z and a belong to Z(S), F lies in S, and Z(S) lies in F because
C_G(F)=F. Moreover C_G(Z(S))=S and N_G(Z(S))=N_G(S). The action of T on
F bounds |S| below by 128, and E=J′ does not centralize a, so S<T.
If a is fused to z, the normalizer condition inside a Sylow subgroup of
C_G(a) forces N_G(S) outside C_G(z). Derived weak closure then excludes
any characteristic subgroup of S containing z from lying in E.

Since [E,a]≤⟨z⟩, E normalizes S. An involution in E outside F acts
nontrivially on Z(S), giving the candidate inverter for the subsequent
order-three argument. The exact center size and omega filtration remain
separate calculations.

Source: Parrott, *A characterization of the Tits' simple group* (1972),
printed p.676, the paragraph beginning “Next consider the case”.
-/

open Subgroup
open scoped commutatorElement

namespace Stellmacher.Recognition.ParrottSecondElementaryData

variable {G : Type*} [Group G] [Finite G] {z : G}

omit [Finite G] in
private theorem local_fixed_join_map (d : ParrottSecondElementaryData z) :
    let H := centralizer ({z} : Set G)
    let DH := (commutator (pCore 2 H)).map (pCore 2 H).subtype
    (zpowers d.a ⊔ (DH ⊓ centralizer ({d.a} : Set H))).map H.subtype = d.F := by
  let H := centralizer ({z} : Set G)
  let J := pCore 2 H
  let DH := (commutator J).map J.subtype
  let E := (commutator J).map (H.subtype.comp J.subtype)
  have hDH : DH.map H.subtype = E := map_map _ _ _
  have hfixed : (DH ⊓ centralizer ({d.a} : Set H)).map H.subtype =
      E ⊓ centralizer ({(d.a : G)} : Set G) := by
    apply le_antisymm
    · rintro b ⟨c, hc, rfl⟩
      exact ⟨hDH ▸ mem_map_of_mem H.subtype hc.1,
        mem_centralizer_singleton_iff.mpr
          (congrArg H.subtype (mem_centralizer_singleton_iff.mp hc.2))⟩
    · intro b hb
      obtain ⟨c, hc, rfl⟩ := hDH.symm ▸ hb.1
      refine ⟨c, ⟨hc, ?_⟩, rfl⟩
      exact mem_centralizer_singleton_iff.mpr
        (Subtype.ext (mem_centralizer_singleton_iff.mp hb.2))
  change (zpowers d.a ⊔ (DH ⊓ centralizer ({d.a} : Set H))).map H.subtype = d.F
  rw [Subgroup.map_sup, MonoidHom.map_zpowers, hfixed]
  exact d.fixed_join.symm

/-- The full centralizer of a inside H lies in the supplied Sylow. -/
public theorem chosen_centralizer_le_sylow (d : ParrottSecondElementaryData z)
    (h : ParrottCentralizerHypotheses z) :
    centralizer ({z} : Set G) ⊓ centralizer ({(d.a : G)} : Set G) ≤
      (d.sylow : Subgroup G) := by
  let H := centralizer ({z} : Set G)
  let J := pCore 2 H
  let DH := (commutator J).map J.subtype
  let FH := zpowers d.a ⊔ (DH ⊓ centralizer ({d.a} : Set H))
  obtain ⟨_, _, _, _, _, hElem, _, _⟩ := parrott_centralizer_structure z h
  let : IsElementaryAbelian 2 (commutator J) := hElem
  let : IsElementaryAbelian 2 DH := IsElementaryAbelian.map J.subtype
  intro x hx
  have hxlocal : (⟨x, hx.1⟩ : H) ∈ normalizer (FH : Set H) := by
    rw [elementary_involution_fixed_join_normalizer DH d.a d.a_order d.a_not_mem_derived]
    apply mem_centralizer_singleton_iff.mpr
    simpa only [map_mul] using congrArg (QuotientGroup.mk' DH)
      (show (⟨x, hx.1⟩ : H) * d.a = d.a * ⟨x, hx.1⟩ from
        Subtype.ext (mem_centralizer_singleton_iff.mp hx.2))
  have hxN : x ∈ normalizer (d.F : Set G) := by
    rw [← d.local_fixed_join_map]
    exact le_normalizer_map H.subtype (mem_map_of_mem H.subtype hxlocal)
  rw [← d.normalizer_inf_centralizer h]
  exact ⟨hxN, hx.1⟩

/-- The two expressions C_T(a) and C_H(a) define the same actual subgroup. -/
public theorem chosen_centralizer_eq (d : ParrottSecondElementaryData z)
    (h : ParrottCentralizerHypotheses z) :
    (d.sylow : Subgroup G) ⊓ centralizer ({(d.a : G)} : Set G) =
      centralizer ({z} : Set G) ⊓ centralizer ({(d.a : G)} : Set G) := by
  exact le_antisymm (inf_le_inf_right _ d.sylow_le_centralizer)
    (le_inf (d.chosen_centralizer_le_sylow h) inf_le_right)

/-- The chosen centralizer is a two-group. -/
public theorem chosen_centralizer_isPGroup (d : ParrottSecondElementaryData z)
    (h : ParrottCentralizerHypotheses z) :
    IsPGroup 2 (centralizer ({z} : Set G) ⊓ centralizer ({(d.a : G)} : Set G) :
      Subgroup G) :=
  d.sylow.isPGroup'.to_le (d.chosen_centralizer_le_sylow h)

omit [Finite G] in
/-- The fixed join lies in the chosen centralizer. -/
public theorem le_chosen_centralizer (d : ParrottSecondElementaryData z) :
    d.F ≤ centralizer ({z} : Set G) ⊓ centralizer ({(d.a : G)} : Set G) := by
  have haF : (d.a : G) ∈ d.F := by
    rw [d.fixed_join]
    exact mem_sup_left (mem_zpowers _)
  let : IsElementaryAbelian 2 d.F := d.elementary
  intro x hx
  refine ⟨d.sylow_le_centralizer (d.le_sylow hx), ?_⟩
  exact mem_centralizer_singleton_iff.mpr
    (congrArg d.F.subtype (mul_comm' (⟨x, hx⟩ : d.F) ⟨d.a, haF⟩))

omit [Finite G] in
/-- Both distinguished involutions are central in S, its center lies in F,
and the ambient centralizer of its center is exactly S. -/
public theorem chosen_centralizer_center (d : ParrottSecondElementaryData z) :
    let S := centralizer ({z} : Set G) ⊓ centralizer ({(d.a : G)} : Set G)
    let Z := (center S).map S.subtype
    z ∈ Z ∧ (d.a : G) ∈ Z ∧ Z ≤ d.F ∧ centralizer (Z : Set G) = S := by
  let S := centralizer ({z} : Set G) ⊓ centralizer ({(d.a : G)} : Set G)
  let Z := (center S).map S.subtype
  have hzS : z ∈ S := d.le_chosen_centralizer d.z_mem_inf.2
  have haS : (d.a : G) ∈ S :=
    ⟨d.a.property, mem_centralizer_singleton_iff.mpr rfl⟩
  have hzZ : z ∈ Z := by
    refine ⟨⟨z, hzS⟩, mem_center_iff.mpr ?_, rfl⟩
    intro s
    exact Subtype.ext (mem_centralizer_singleton_iff.mp s.property.1)
  have haZ : (d.a : G) ∈ Z := by
    refine ⟨⟨d.a, haS⟩, mem_center_iff.mpr ?_, rfl⟩
    intro s
    exact Subtype.ext (mem_centralizer_singleton_iff.mp s.property.2)
  refine ⟨hzZ, haZ, ?_, ?_⟩
  · rw [← d.centralizer_eq]
    rintro x ⟨s, hs, rfl⟩ f hf
    exact congrArg S.subtype (mem_center_iff.mp hs ⟨f, d.le_chosen_centralizer hf⟩)
  · apply le_antisymm
    · intro x hx
      exact ⟨mem_centralizer_singleton_iff.mpr (hx z hzZ).symm,
        mem_centralizer_singleton_iff.mpr (hx d.a haZ).symm⟩
    · intro s hs c hc
      obtain ⟨c, hc, rfl⟩ := hc
      exact (congrArg S.subtype (mem_center_iff.mp hc ⟨s, hs⟩)).symm

/-- The chosen centralizer is properly smaller than the supplied Sylow. -/
public theorem chosen_centralizer_card_lt (d : ParrottSecondElementaryData z)
    (h : ParrottCentralizerHypotheses z) :
    Nat.card (centralizer ({z} : Set G) ⊓ centralizer ({(d.a : G)} : Set G) :
      Subgroup G) < Nat.card d.sylow := by
  let H := centralizer ({z} : Set G)
  let J := pCore 2 H
  let E := (commutator J).map (H.subtype.comp J.subtype)
  let S := H ⊓ centralizer ({(d.a : G)} : Set G)
  have hET : E ≤ (d.sylow : Subgroup G) := by
    rw [d.sylow_map]
    dsimp only [E]
    rw [← map_map]
    exact map_mono ((map_subtype_le _).trans
      (pCore_isPGroup.le_sylow_of_normal d.localSylow))
  have haE : (d.a : G) ∉ E := by
    rintro ⟨a, ha, heq⟩
    apply d.a_not_mem_derived
    exact ⟨a, ha, H.subtype_injective heq⟩
  change Nat.card S < Nat.card d.sylow
  by_contra hlt
  have hST : S = (d.sylow : Subgroup G) :=
    eq_of_le_of_card_ge (d.chosen_centralizer_le_sylow h) (Nat.le_of_not_gt hlt)
  apply haE
  change (d.a : G) ∈ (commutator J).map (H.subtype.comp J.subtype)
  rw [← parrott_derived_centralizer z h]
  intro e he
  exact mem_centralizer_singleton_iff.mp ((hST.symm ▸ hET he : e ∈ S).2)

/-- Fusion with z forces the normalizer of the chosen centralizer to move z.
This follows from the normalizer condition in a Sylow subgroup of C_G(a). -/
public theorem chosen_centralizer_normalizer_not_le (d : ParrottSecondElementaryData z)
    (h : ParrottCentralizerHypotheses z) (hconj : IsConj z (d.a : G)) :
    let S := centralizer ({z} : Set G) ⊓ centralizer ({(d.a : G)} : Set G)
    ¬ normalizer (S : Set G) ≤ centralizer ({z} : Set G) := by
  classical
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let H := centralizer ({z} : Set G)
  let C := centralizer ({(d.a : G)} : Set G)
  let S := H ⊓ C
  change ¬ normalizer (S : Set G) ≤ H
  have hCcard : Nat.card C = Nat.card H := by
    obtain ⟨c, hc⟩ := isConj_iff.mp hconj
    let f : G ≃* G := MulAut.conj c
    have hfz : f z = (d.a : G) := hc
    apply (Nat.card_congr (Equiv.subtypeEquiv f.toEquiv ?_)).symm
    intro a
    change a ∈ H ↔ f a ∈ C
    change a ∈ centralizer ({z} : Set G) ↔
      f a ∈ centralizer ({(d.a : G)} : Set G)
    simp only [mem_centralizer_singleton_iff]
    constructor
    · intro ha
      simpa only [map_mul, hfz] using congrArg f ha
    · intro ha
      apply f.injective
      simpa only [map_mul, hfz] using ha
  let K := S.subgroupOf C
  have hKC : K.map C.subtype = S := map_subgroupOf_eq_of_le inf_le_right
  have hKcard : Nat.card K = Nat.card S :=
    Nat.card_congr (subgroupOfEquivOfLe (show S ≤ C from inf_le_right)).toEquiv
  have hKp : IsPGroup 2 K := (d.chosen_centralizer_isPGroup h).comap_subtype
  obtain ⟨T, hKT⟩ := hKp.exists_le_sylow
  have hTcard : Nat.card T = Nat.card d.sylow := by
    rw [T.card_eq_multiplicity, hCcard, (h.card_and_solvable z).1, d.sylow_card h]
    decide +kernel
  have hproper : K.subgroupOf (T : Subgroup C) < ⊤ := by
    rw [lt_top_iff_ne_top, Ne, subgroupOf_eq_top]
    intro hTK
    have hh := card_le_of_le hTK
    rw [hKcard, hTcard] at hh
    exact (not_le_of_gt (d.chosen_centralizer_card_lt h)) hh
  let : Group.IsNilpotent T := T.isPGroup'.isNilpotent
  have hlt := Group.normalizerCondition_of_isNilpotent
    (K.subgroupOf (T : Subgroup C)) hproper
  obtain ⟨u, huN, huK⟩ := SetLike.exists_of_lt hlt
  have huNK : (u : C) ∈ normalizer (K : Set C) := by
    rw [← subgroupOf_normalizer_eq hKT] at huN
    exact huN
  have hgS : ((u : C) : G) ∈ normalizer (S : Set G) := by
    rw [← hKC]
    exact K.le_normalizer_map C.subtype (mem_map_of_mem C.subtype huNK)
  intro hle
  exact huK ⟨hle hgS, (u : C).property⟩

/-- Under derived weak closure, a characteristic subgroup of the chosen
centralizer that contains z cannot be contained in the ambient derived core. -/
public theorem chosen_characteristic_not_le_derived (d : ParrottSecondElementaryData z)
    (h : ParrottCentralizerHypotheses z) (hconj : IsConj z (d.a : G))
    (hderived : ∀ t : G, t ∈ (commutator (pCore 2 (centralizer ({z} : Set G)))).map
      ((centralizer ({z} : Set G)).subtype.comp
        (pCore 2 (centralizer ({z} : Set G))).subtype) → IsConj z t → t = z) :
    let S := centralizer ({z} : Set G) ⊓ centralizer ({(d.a : G)} : Set G)
    ∀ K : Subgroup S, K.Characteristic → z ∈ K.map S.subtype →
      ¬ K.map S.subtype ≤ (commutator (pCore 2 (centralizer ({z} : Set G)))).map
        ((centralizer ({z} : Set G)).subtype.comp
          (pCore 2 (centralizer ({z} : Set G))).subtype) := by
  let S := centralizer ({z} : Set G) ⊓ centralizer ({(d.a : G)} : Set G)
  change ∀ K : Subgroup S, K.Characteristic → z ∈ K.map S.subtype → _
  intro K hK hzK hKE
  apply d.chosen_centralizer_normalizer_not_le h hconj
  intro g hg
  obtain ⟨s, hs, hsz⟩ := hzK
  change (s : G) = z at hsz
  let f : MulAut S := S.normalizerMonoidHom ⟨g, hg⟩
  have hfs : f s ∈ K := by
    change s ∈ K.comap f.toMonoidHom
    rw [hK.fixed f]
    exact hs
  have hgz : g * z * g⁻¹ ∈ K.map S.subtype := by
    have hm := mem_map_of_mem S.subtype hfs
    change g * (s : G) * g⁻¹ ∈ K.map S.subtype at hm
    rwa [hsz] at hm
  have heq : g * z * g⁻¹ = z :=
    hderived _ (hKE hgz) (isConj_iff.mpr ⟨g, rfl⟩)
  exact mem_centralizer_singleton_iff.mpr (mul_inv_eq_iff_eq_mul.mp heq)

/-- If F is self-normalized by the supplied Sylow, fusion forces the
normalizer of S to contain an element that does not normalize F. -/
public theorem chosen_centralizer_normalizer_not_le_fixed_join_normalizer
    (d : ParrottSecondElementaryData z) (h : ParrottCentralizerHypotheses z)
    (hself : normalizer (d.F : Set G) = (d.sylow : Subgroup G))
    (hconj : IsConj z (d.a : G)) :
    let S := centralizer ({z} : Set G) ⊓ centralizer ({(d.a : G)} : Set G)
    ¬ normalizer (S : Set G) ≤ normalizer (d.F : Set G) := by
  dsimp only
  intro hle
  rw [hself] at hle
  exact d.chosen_centralizer_normalizer_not_le h hconj
    (hle.trans d.sylow_le_centralizer)

omit [Finite G] in
/-- The center of the chosen centralizer has exactly the same ambient normalizer. -/
public theorem chosen_centralizer_center_normalizer (d : ParrottSecondElementaryData z) :
    let S := centralizer ({z} : Set G) ⊓ centralizer ({(d.a : G)} : Set G)
    normalizer (((center S).map S.subtype : Subgroup G) : Set G) =
      normalizer (S : Set G) := by
  let S := centralizer ({z} : Set G) ⊓ centralizer ({(d.a : G)} : Set G)
  let Z := (center S).map S.subtype
  have hcentral : centralizer (Z : Set G) = S := d.chosen_centralizer_center.2.2.2
  change normalizer (Z : Set G) = normalizer (S : Set G)
  apply le_antisymm
  · have hNC : normalizer (Z : Set G) ≤ normalizer (centralizer (Z : Set G) : Set G) := by
      apply le_normalizer_iff.mpr
      intro g hg x hx c hc
      have hc' : g⁻¹ * c * g ∈ Z := by
        have hh : g⁻¹ * c * (g⁻¹)⁻¹ ∈ Z :=
          ((normalizer (Z : Set G)).inv_mem hg c).mp hc
        rwa [inv_inv] at hh
      have hcomm := hx _ hc'
      calc
        c * (g * x * g⁻¹) = g * ((g⁻¹ * c * g) * x) * g⁻¹ := by group
        _ = g * (x * (g⁻¹ * c * g)) * g⁻¹ := by rw [hcomm]
        _ = (g * x * g⁻¹) * c := by group
    exact hNC.trans_eq (congrArg (fun U : Subgroup G => normalizer (U : Set G)) hcentral)
  · apply le_normalizer_iff.mpr
    intro g hg x hx
    obtain ⟨s, hs, rfl⟩ := hx
    let f : MulAut S := S.normalizerMonoidHom ⟨g, hg⟩
    have hfs : f s ∈ center S := by
      change s ∈ (center S).comap f.toMonoidHom
      rw [(inferInstance : (center S).Characteristic).fixed f]
      exact hs
    exact ⟨f s, hfs, rfl⟩

/-- The derived two-core normalizes the chosen centralizer: conjugating a
by an element of E changes it only by a power of the central involution z. -/
public theorem derived_le_chosen_centralizer_normalizer (d : ParrottSecondElementaryData z)
    (h : ParrottCentralizerHypotheses z) :
    let H := centralizer ({z} : Set G)
    let J := pCore 2 H
    let E := (commutator J).map (H.subtype.comp J.subtype)
    let S := H ⊓ centralizer ({(d.a : G)} : Set G)
    E ≤ normalizer (S : Set G) := by
  let H := centralizer ({z} : Set G)
  let J := pCore 2 H
  let E := (commutator J).map (H.subtype.comp J.subtype)
  let S := H ⊓ centralizer ({(d.a : G)} : Set G)
  change E ≤ normalizer (S : Set G)
  obtain ⟨hZ, _, _, _, hupper, _, _, _⟩ := parrott_centralizer_structure z h
  have hcomm (e : G) (he : e ∈ E) : ⁅e, (d.a : G)⁆ ∈ zpowers z := by
    obtain ⟨b, hb, rfl⟩ := he
    have hbc : ⁅b, (⟨d.a, d.a_mem_core⟩ : J)⁆ ∈ center J := by
      have hbU : b ∈ Subgroup.upperCentralSeries J 2 := hupper ▸ hb
      simpa only [Subgroup.upperCentralSeries_one] using
        (Subgroup.mem_upperCentralSeries_succ_iff.mp hbU (⟨d.a, d.a_mem_core⟩ : J))
    rw [← hZ]
    exact mem_map_of_mem (H.subtype.comp J.subtype) hbc
  apply le_normalizer_iff.mpr
  intro e he s hs
  have heH : e ∈ H := by
    obtain ⟨b, _, rfl⟩ := he
    exact b.val.property
  refine ⟨H.mul_mem (H.mul_mem heH hs.1) (H.inv_mem heH), ?_⟩
  have hzCs : zpowers z ≤ centralizer ({s} : Set G) :=
    zpowers_le.mpr (mem_centralizer_singleton_iff.mpr
      (mem_centralizer_singleton_iff.mp hs.1).symm)
  have hc : Commute ⁅e⁻¹, (d.a : G)⁆ s :=
    mem_centralizer_singleton_iff.mp (hzCs (hcomm _ (E.inv_mem he)))
  have ha : Commute (d.a : G) s := (mem_centralizer_singleton_iff.mp hs.2).symm
  have hcomm' : (e⁻¹ * (d.a : G) * e) * s = s * (e⁻¹ * (d.a : G) * e) := by
    simpa only [commutatorElement_def, inv_inv, mul_assoc, inv_mul_cancel, mul_one]
      using (hc.mul_left ha).eq
  apply mem_centralizer_singleton_iff.mpr
  calc
    (e * s * e⁻¹) * (d.a : G) = e * (s * (e⁻¹ * (d.a : G) * e)) * e⁻¹ := by group
    _ = e * ((e⁻¹ * (d.a : G) * e) * s) * e⁻¹ := by rw [hcomm']
    _ = (d.a : G) * (e * s * e⁻¹) := by group

/-- The action of T on the nonidentity elements of F forces |S| ≥ 128. -/
public theorem chosen_centralizer_card_ge (d : ParrottSecondElementaryData z)
    (h : ParrottCentralizerHypotheses z) :
    128 ≤ Nat.card (centralizer ({z} : Set G) ⊓
      centralizer ({(d.a : G)} : Set G) : Subgroup G) := by
  classical
  let T : Subgroup G := d.sylow
  let S := centralizer ({z} : Set G) ⊓ centralizer ({(d.a : G)} : Set G)
  have hST : S ≤ T := d.chosen_centralizer_le_sylow h
  let : MulDistribMulAction T d.F :=
    Subgroup.conjMulDistribMulActionOfLeNormalizer T d.F d.sylow_le_normalizer
  have haF : (d.a : G) ∈ d.F := by
    rw [d.fixed_join]
    exact mem_sup_left (mem_zpowers _)
  let aF : d.F := ⟨d.a, haF⟩
  have haFne : aF ≠ 1 := by
    intro heq
    have haone : (d.a : G) = 1 := congrArg Subtype.val heq
    have ha : d.a = 1 := Subtype.ext haone
    have ho := d.a_order
    simp [ha] at ho
  have hsub : MulAction.orbit T aF ⊆ ({1} : Set d.F)ᶜ := by
    intro x hx
    obtain ⟨t, rfl⟩ := MulAction.mem_orbit_iff.mp hx
    change t • aF ≠ 1
    intro heq
    apply haFne
    simpa using congrArg (fun y : d.F => t⁻¹ • y) heq
  have hbound : Nat.card (MulAction.orbit T aF) ≤ 31 := by
    have hc : (({1} : Set d.F)ᶜ).ncard = 31 := by
      rw [Set.ncard_compl, d.card, Set.ncard_singleton]
    exact (Set.ncard_le_ncard hsub).trans_eq hc
  have hstab : MulAction.stabilizer T aF = S.subgroupOf T := by
    ext t
    rw [MulAction.mem_stabilizer_iff, Subtype.ext_iff]
    change (t : G) * (d.a : G) * (t : G)⁻¹ = (d.a : G) ↔ (t : G) ∈ S
    rw [mul_inv_eq_iff_eq_mul, ← mem_centralizer_singleton_iff]
    exact (and_iff_right (d.sylow_le_centralizer t.property)).symm
  have hindex : (S.subgroupOf T).index ≤ 31 := by
    rw [← hstab, MulAction.index_stabilizer]
    exact hbound
  have hcard : (S.subgroupOf T).index * Nat.card S = 2048 := by
    have hc := (S.subgroupOf T).index_mul_card
    rw [Nat.card_congr (subgroupOfEquivOfLe hST).toEquiv, d.sylow_card h] at hc
    exact hc
  obtain ⟨n, hn⟩ := (d.chosen_centralizer_isPGroup h).exists_card_eq
  change Nat.card S = 2 ^ n at hn
  have hnge : 7 ≤ n := by
    by_contra hlt
    have hp : 2 ^ n ≤ 2 ^ 6 := Nat.pow_le_pow_right (by decide) (by omega)
    rw [hn] at hcard
    norm_num at hp
    nlinarith
  change 128 ≤ Nat.card S
  rw [hn]
  exact Nat.pow_le_pow_right (by decide : 0 < 2) hnge

/-- There is an involution in E outside F. It normalizes S and acts
nontrivially on its center. This is the candidate inverter in the source. -/
public theorem chosen_centralizer_exists_center_moving_involution
    (d : ParrottSecondElementaryData z) (h : ParrottCentralizerHypotheses z) :
    let H := centralizer ({z} : Set G)
    let J := pCore 2 H
    let E := (commutator J).map (H.subtype.comp J.subtype)
    let S := H ⊓ centralizer ({(d.a : G)} : Set G)
    let Z := (center S).map S.subtype
    ∃ w : G, w ∈ E ∧ w ∉ d.F ∧ orderOf w = 2 ∧
      w ∈ normalizer (S : Set G) ∧ w ∉ centralizer (Z : Set G) := by
  let H := centralizer ({z} : Set G)
  let J := pCore 2 H
  let E := (commutator J).map (H.subtype.comp J.subtype)
  let S := H ⊓ centralizer ({(d.a : G)} : Set G)
  let Z := (center S).map S.subtype
  change ∃ w : G, w ∈ E ∧ w ∉ d.F ∧ orderOf w = 2 ∧
    w ∈ normalizer (S : Set G) ∧ w ∉ centralizer (Z : Set G)
  obtain ⟨_, _, _, _, _, hElem, hDcard, _⟩ := parrott_centralizer_structure z h
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let : IsElementaryAbelian 2 (commutator J) := hElem
  let : IsElementaryAbelian 2 E := IsElementaryAbelian.map (H.subtype.comp J.subtype)
  have hEcard : Nat.card E = 32 :=
    (card_map_of_injective (K := commutator J) (f := H.subtype.comp J.subtype)
      (H.subtype_injective.comp J.subtype_injective)).trans hDcard
  have hnot : ¬ E ≤ d.F := by
    intro hle
    have hc := d.inf_card
    rw [inf_eq_left.mpr hle, hEcard] at hc
    omega
  obtain ⟨w, hwE, hwF⟩ := SetLike.not_le_iff_exists.mp hnot
  refine ⟨w, hwE, hwF, orderOf_eq_prime
    (elemPow_eq_one_of_isElementaryAbelian w hwE)
    (fun heq => hwF (heq ▸ d.F.one_mem)),
    d.derived_le_chosen_centralizer_normalizer h hwE, ?_⟩
  intro hwC
  have hcentral : centralizer (Z : Set G) = S := d.chosen_centralizer_center.2.2.2
  have hwS : w ∈ S := hcentral ▸ hwC
  have hwEF : w ∈ E ⊓ d.F := d.inf_eq.symm ▸ ⟨hwE, hwS.2⟩
  exact hwF hwEF.2

/-- The N₂ hypothesis makes the actual normalizer of S solvable. -/
public theorem chosen_centralizer_normalizer_solvable
    (d : ParrottSecondElementaryData z) (h : ParrottCentralizerHypotheses z)
    (hN : IsNTwoGroup G) :
    let S := centralizer ({z} : Set G) ⊓ centralizer ({(d.a : G)} : Set G)
    Group.IsSolvable (normalizer (S : Set G)) := by
  let S := centralizer ({z} : Set G) ⊓ centralizer ({(d.a : G)} : Set G)
  have hne : S ≠ ⊥ := by
    intro heq
    have hc := d.chosen_centralizer_card_ge h
    change 128 ≤ Nat.card S at hc
    rw [heq, card_bot] at hc
    omega
  exact hN _ ⟨S, hne, d.chosen_centralizer_isPGroup h, rfl⟩

end Stellmacher.Recognition.ParrottSecondElementaryData
