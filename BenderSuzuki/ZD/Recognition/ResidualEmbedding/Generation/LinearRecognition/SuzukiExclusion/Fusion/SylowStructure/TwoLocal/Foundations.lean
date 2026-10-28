module
public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.Generation.LinearRecognition.SuzukiExclusion.Fusion.SylowStructure.Factorization
public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.Generation.LinearRecognition.SuzukiExclusion.Fusion.SylowStructure.TwoLocalContract
public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.Generation.LinearRecognition.SuzukiExclusion.LocalGeometry.Borel
public import Theory.GroupTheory.DisjointConjugateCenter

/-!
# The center, torus action and coset kernels for Suzuki Lemma 14.6

Write A = closure (Z ∩ M), P for the marked Borel two-core and K for the
split torus. The supplied direct product T = P × U gives Z(T) = A × U.
The concrete Suzuki root calculation also gives [T,T] = A. Consequently
N_G(T) lies in M. For each nonidentity u in U, the literal coset Au has
pointwise centralizer T and its set stabilizer lies in N_G(T).

Torus semiregularity and P ∩ D = 1 imply that K acts freely on A minus
identity. Counting gives regularity there, and hence on Au minus u.
This proves the needed torus action without assuming that K normalizes S.
The global order formula proves that the actual quotient S/T having order
q is sufficient to make S an ambient Sylow subgroup.

These are supporting results, not the completed Lemma 14.6: construction
of the translation isomorphism S/T ≃ A and the subsequent normality and
orbit argument remain separate. Source: GLS4, Chapter 2, (14B)–(14C) and
Lemma 14.6, `refs/KGroup/GLS4/Chapter2.tex`, approximately lines 2540–2580.
The root derived-center identity uses the existing proof of
Huppert–Blackburn III, XI.3.1 through the actual marked matrix equivalence.
-/

noncomputable section
namespace BenderSuzuki.ZD.SuzukiExclusion
open Subgroup Theory.GroupTheory PFAppendixIII PFchapter1section1
open scoped Pointwise commutatorElement
universe u
variable {G : Type u} [Group G] [Finite G] {Z : Set G} {M : Subgroup G}
  {z t : G} {m : ℕ}

public theorem LocalGeometry.P_le_T (g : LocalGeometry Z M z t m) :
    borelTwoCore M z t ≤ g.T := by rw [g.P_eq]; exact inf_le_left

public theorem LocalGeometry.U_le_T (g : LocalGeometry Z M z t m) : g.U ≤ g.T := by
  rw [g.U_eq]; exact inf_le_left

public theorem LocalGeometry.U_le_residual_centralizer (g : LocalGeometry Z M z t m) :
    g.U ≤ centralizer (residualGenerated M z t : Set G) := by
  rw [g.U_eq]; exact inf_le_right

public theorem LocalGeometry.A_le_P (g : LocalGeometry Z M z t m) :
    closure (Z ∩ (M : Set G)) ≤ borelTwoCore M z t := by
  rw [← g.P_center]; exact map_subtype_le _

public theorem LocalGeometry.T_eq_sup (g : LocalGeometry Z M z t m) :
    g.T = borelTwoCore M z t ⊔ g.U := by
  apply le_antisymm
  · intro x hx
    obtain ⟨p, hp, u, hu, rfl⟩ := (Set.ext_iff.mp g.T_product x).mp hx
    exact mul_mem_sup hp hu
  · exact sup_le g.P_le_T g.U_le_T

public theorem LocalGeometry.P_centralizes_U (g : LocalGeometry Z M z t m) :
    borelTwoCore M z t ≤ centralizer (g.U : Set G) :=
  le_centralizer_iff.mp (g.U_le_residual_centralizer.trans
    (centralizer_le (by rw [g.P_eq]; exact inf_le_right)))

public theorem LocalGeometry.U_le_center_T (g : LocalGeometry Z M z t m) :
    g.U ≤ (center g.T).map g.T.subtype := by
  let := g.U_elementary
  rw [← centerIn_eq_map_center]
  apply le_inf g.U_le_T
  apply le_centralizer_iff.mpr
  rw [g.T_eq_sup]
  exact sup_le g.P_centralizes_U g.U.le_centralizer

public theorem LocalGeometry.T_center (g : LocalGeometry Z M z t m) :
    (center g.T).map g.T.subtype = closure (Z ∩ (M : Set G)) ⊔ g.U := by
  have hAC : closure (Z ∩ (M : Set G)) ≤ (center g.T).map g.T.subtype := by
    rw [← centerIn_eq_map_center]
    apply le_inf (g.A_le_P.trans g.P_le_T)
    apply le_centralizer_iff.mpr
    rw [g.T_eq_sup]
    exact sup_le g.borelTwoCore_le_distinguished_centralizer
      (le_centralizer_iff.mp (g.A_le_P.trans g.P_centralizes_U))
  apply le_antisymm ?_ (sup_le hAC g.U_le_center_T)
  intro x hx
  have hxT := map_subtype_le _ hx
  obtain ⟨p, hp, v, hv, rfl⟩ := (Set.ext_iff.mp g.T_product x).mp hxT
  have hpZ : p ∈ (center g.T).map g.T.subtype := by
    have hh := ((center g.T).map g.T.subtype).mul_mem hx
      (((center g.T).map g.T.subtype).inv_mem (g.U_le_center_T hv))
    simpa only [mul_inv_cancel_right] using hh
  have hpA : p ∈ closure (Z ∩ (M : Set G)) := by
    rw [← g.P_center, ← centerIn_eq_map_center]
    rw [← centerIn_eq_map_center] at hpZ
    exact ⟨hp, centralizer_le g.P_le_T hpZ.2⟩
  exact mul_mem_sup hpA hv

public theorem Context.U_ne_bot (d : Context Z M z t m) (g : LocalGeometry Z M z t m) :
    g.U ≠ ⊥ := by
  obtain ⟨V, hV⟩ := g.U_sylow_pair
  intro he
  apply V.ne_bot_of_dvd_card d.even_pair.two_dvd
  apply map_injective (residualPairStabilizer M t).subtype_injective
  simpa only [hV, Subgroup.map_bot] using he

public theorem Context.T_center_elementary (d : Context Z M z t m)
    (g : LocalGeometry Z M z t m) :
    IsElementaryAbelian 2 ((center g.T).map g.T.subtype) := by
  rw [g.T_center]
  let := d.distinguished_elementary_card.1
  let := g.U_elementary
  exact IsElementaryAbelian.sup_of_le_centralizer
    (le_centralizer_iff.mp (g.A_le_P.trans g.P_centralizes_U))

public theorem Context.T_center_centralizer (d : Context Z M z t m)
    (g : LocalGeometry Z M z t m) :
    centralizer (((center g.T).map g.T.subtype : Subgroup G) : Set G) = g.T := by
  apply le_antisymm
  · obtain ⟨u, hu, hune⟩ := g.U.bot_or_exists_ne_one.resolve_left (d.U_ne_bot g)
    rw [g.T_center]
    intro x hx
    rw [← g.centralizer_U u hu hune]
    exact ⟨centralizer_le
      (show closure (Z ∩ (M : Set G)) ≤ closure (Z ∩ (M : Set G)) ⊔ g.U from le_sup_left) hx,
      centralizer_le (by
        intro v hv
        rw [Set.mem_singleton_iff] at hv
        subst v
        exact mem_sup_right hu) hx⟩
  · apply le_centralizer_iff.mpr
    rw [← centerIn_eq_map_center]
    exact inf_le_right

public theorem Context.S_inf_centralizer_U (d : Context Z M z t m)
    (g : LocalGeometry Z M z t m) (hsemi : TorusSemiregular M t)
    {u : G} (hu : u ∈ g.U) (hune : u ≠ 1) :
    g.S ⊓ centralizer ({u} : Set G) = g.T := by
  apply le_antisymm
  · rw [← g.centralizer_U u hu hune]
    exact inf_le_inf (d.S_le_distinguished_centralizer g hsemi) le_rfl
  · refine le_inf g.T_lt_S.le ?_
    rw [← g.centralizer_U u hu hune]
    exact inf_le_right

public theorem Context.torus_le_normalizer_distinguished (d : Context Z M z t m) :
    residualCommutator M t ≤ normalizer (closure (Z ∩ (M : Set G)) : Set G) := by
  rw [distinguishedClosure_normalizer d.minimal.disconnected, d.torus_eq_local_pair]
  exact inf_le_left.trans inf_le_left

/-- The literal torus conjugation fixes no nonidentity distinguished element. -/
public theorem Context.torus_conj_distinguished_free (d : Context Z M z t m)
    (g : LocalGeometry Z M z t m) (hsemi : TorusSemiregular M t)
    {k a : G} (hk : k ∈ residualCommutator M t)
    (ha : a ∈ closure (Z ∩ (M : Set G))) (ha1 : a ≠ 1)
    (hfix : MulAut.conj k a = a) : k = 1 := by
  by_contra hk1
  have hcomm : k * a = a * k := by
    have hh := congrArg (fun v : G => v * k) hfix
    simpa only [MulAut.conj_apply, mul_assoc, inv_mul_cancel, mul_one] using hh
  have haD := d.torus_centralizer_le_pair hsemi hk hk1
    ⟨g.S_le_M (g.T_lt_S.le (g.P_le_T (g.A_le_P ha))),
      mem_centralizer_singleton_iff.mpr hcomm.symm⟩
  exact ha1 (disjoint_def.mp d.borelTwoCore_disjoint_pair (g.A_le_P ha) haD)

/-- The torus is regular on the nonidentity elements of the actual A. -/
public theorem Context.torus_regular_distinguished (d : Context Z M z t m)
    (g : LocalGeometry Z M z t m) (hsemi : TorusSemiregular M t)
    {a b : G} (ha : a ∈ closure (Z ∩ (M : Set G))) (ha1 : a ≠ 1)
    (hb : b ∈ closure (Z ∩ (M : Set G))) (hb1 : b ≠ 1) :
    ∃! k : residualCommutator M t, MulAut.conj (k : G) a = b := by
  classical
  let A := closure (Z ∩ (M : Set G))
  let K := residualCommutator M t
  let φ : K → {v : A // v ≠ 1} := fun k =>
    ⟨⟨MulAut.conj (k : G) a,
      (d.torus_le_normalizer_distinguished k.property a).mp ha⟩, by
      intro hh
      apply ha1
      exact (MulAut.conj (k : G)).injective
        ((congrArg (fun v : A => (v : G)) hh).trans (map_one _).symm)⟩
  have hi : Function.Injective φ := by
    intro k l he
    have hh : MulAut.conj (k : G) a = MulAut.conj (l : G) a :=
      congrArg (fun v : {v : A // v ≠ 1} => ((v.val : A) : G)) he
    have hfix : MulAut.conj ((l : G)⁻¹ * k) a = a := by
      change ((l : G)⁻¹ * k) * a * ((l : G)⁻¹ * k)⁻¹ = a
      calc
        _ = (l : G)⁻¹ * (MulAut.conj (k : G) a) * l := by
          simp only [MulAut.conj_apply]; group
        _ = (l : G)⁻¹ * (MulAut.conj (l : G) a) * l := by rw [hh]
        _ = a := by simp [MulAut.conj_apply, mul_assoc]
    have hone := d.torus_conj_distinguished_free g hsemi
      (K.mul_mem (K.inv_mem l.property) k.property) ha ha1 hfix
    exact Subtype.ext (inv_mul_eq_one.mp hone).symm
  have hc : Nat.card K = Nat.card {v : A // v ≠ 1} := by
    let : Fintype A := Fintype.ofFinite A
    rw [Nat.card_eq_fintype_card (α := {v : A // v ≠ 1}),
      Fintype.card_subtype_compl,
      show Fintype.card {v : A // v = 1} = 1 from Fintype.card_unique,
      ← Nat.card_eq_fintype_card]
    rw [show Nat.card A = 2 ^ (2 * m + 1) from d.distinguished_elementary_card.2]
    exact d.torus_card
  obtain ⟨k, hk⟩ := ((Nat.bijective_iff_injective_and_card φ).mpr ⟨hi, hc⟩).surjective
    ⟨⟨b, hb⟩, fun h => hb1 (congrArg Subtype.val h)⟩
  have hk' : MulAut.conj (k : G) a = b :=
    congrArg (fun v : {v : A // v ≠ 1} => ((v.val : A) : G)) hk
  refine ⟨k, hk', fun l hl => hi ?_⟩
  exact Subtype.ext (Subtype.ext (hl.trans hk'.symm))

private theorem root_commutator_eq_center (m : ℕ) (hm : 0 < m) :
    _root_.commutator (MatrixGroups.SuzukiRootSubgroup m) =
      center (MatrixGroups.SuzukiRootSubgroup m) := by
  open _root_.BenderSuzuki.MatrixGroups in
    let F := BinaryGaloisField (2 * m + 1)
    let σ : F ≃+* F := iterateFrobeniusEquiv F 2 (m + 1)
    obtain ⟨_, _, _, _, _, _, _, _, _, hc, _⟩ :=
      External.huppert_blackburn_XI_3_1 m hm σ
        (External.binaryGaloisField_tits_formula_sq m σ
          (iterateFrobeniusEquiv_def F 2 (m + 1)))
    change _root_.commutator (SuzukiRootClosure m) = center (SuzukiRootClosure m) at hc
    let e : SuzukiRootSubgroup m ≃* SuzukiRootClosure m :=
      subgroupOfEquivOfLe (suzukiRootClosure_le m)
    have hz : (center (SuzukiRootSubgroup m)).map e.toMonoidHom =
        center (SuzukiRootClosure m) := by
      ext x
      constructor
      · rintro ⟨y, hy, rfl⟩
        exact (centerCongr e ⟨y, hy⟩).property
      · intro hx
        exact ⟨e.symm x, (centerCongr e.symm ⟨x, hx⟩).property, e.apply_symm_apply x⟩
    apply map_injective (f := e.toMonoidHom) e.injective
    rw [hz, map_commutator_eq, MonoidHom.range_eq_top.mpr e.surjective]
    exact hc

/-- The concrete root-group calculation identifies the characteristic subgroup A. -/
public theorem Context.P_commutator (d : Context Z M z t m)
    (g : LocalGeometry Z M z t m) :
    ⁅borelTwoCore M z t, borelTwoCore M z t⁆ = closure (Z ∩ (M : Set G)) := by
  obtain ⟨f, _, hP, _⟩ := d.borel_marking
  let φ := (residualGenerated M z t).subtype.comp f.toMonoidHom
  have hi : Function.Injective φ := Subtype.val_injective.comp f.injective
  calc
    ⁅borelTwoCore M z t, borelTwoCore M z t⁆ =
        (⁅MatrixGroups.SuzukiRootSubgroup m, MatrixGroups.SuzukiRootSubgroup m⁆).map φ := by
      rw [map_commutator, hP]
    _ = ((center (MatrixGroups.SuzukiRootSubgroup m)).map
        (MatrixGroups.SuzukiRootSubgroup m).subtype).map φ := by
      rw [← map_subtype_commutator, root_commutator_eq_center m d.parameter_pos]
    _ = (center (borelTwoCore M z t)).map (borelTwoCore M z t).subtype := by
      rw [map_embeddedCenter _ _ hi, hP]
    _ = _ := g.P_center

/-- Since U is central in T, the derived subgroup of T is exactly A. -/
public theorem Context.T_commutator (d : Context Z M z t m)
    (g : LocalGeometry Z M z t m) : ⁅g.T, g.T⁆ = closure (Z ∩ (M : Set G)) := by
  rw [← d.P_commutator g]
  apply le_antisymm ?_ (commutator_mono g.P_le_T g.P_le_T)
  apply commutator_le.mpr
  intro x hx y hy
  obtain ⟨p, hp, u, hu, rfl⟩ := (Set.ext_iff.mp g.T_product x).mp hx
  obtain ⟨q, hq, v, hv, rfl⟩ := (Set.ext_iff.mp g.T_product y).mp hy
  have huC : u ∈ centralizer (g.T : Set G) := by
    have h := g.U_le_center_T hu
    rw [← centerIn_eq_map_center] at h
    exact h.2
  have hvC : v ∈ centralizer (g.T : Set G) := by
    have h := g.U_le_center_T hv
    rw [← centerIn_eq_map_center] at h
    exact h.2
  have huc : ⁅u, q * v⁆ = 1 := commutatorElement_eq_one_iff_mul_comm.mpr
    (huC _ (g.T.mul_mem (g.P_le_T hq) (g.U_le_T hv))).symm
  have hvc : ⁅p, v⁆ = 1 := commutatorElement_eq_one_iff_mul_comm.mpr
    (hvC _ (g.P_le_T hp))
  rw [commutatorElement_mul_left_eq_conj_mul, huc, mul_one, mul_inv_cancel,
    one_mul, commutatorElement_mul_right_eq_mul_conj, hvc, mul_one, mul_inv_cancel_right]
  exact commutator_mem_commutator hp hq

/-- Every normalizer element preserves A = [T,T], hence lies in M. -/
public theorem Context.normalizer_T_le_M (d : Context Z M z t m)
    (g : LocalGeometry Z M z t m) : normalizer (g.T : Set G) ≤ M := by
  apply le_trans ?_ (distinguishedClosure_normalizer d.minimal.disconnected).le
  intro x hx
  apply mem_normalizer_iff_map_conj_eq.mpr
  rw [← d.T_commutator g, map_commutator,
    mem_normalizer_iff_map_conj_eq.mp hx]

/-- The torus centralizes the actual second direct factor U. -/
public theorem Context.torus_centralizes_U (d : Context Z M z t m)
    (g : LocalGeometry Z M z t m) :
    residualCommutator M t ≤ centralizer (g.U : Set G) := by
  have hKL : residualCommutator M t ≤ residualGenerated M z t := by
    rw [d.torus_eq_local_pair]
    exact inf_le_right
  exact hKL.trans (le_centralizer_iff.mp g.U_le_residual_centralizer)

/-- Torus normalization of T follows before, and does not assume, normalization of S. -/
public theorem Context.torus_normalizes_T (d : Context Z M z t m)
    (g : LocalGeometry Z M z t m) :
    residualCommutator M t ≤ normalizer (g.T : Set G) := by
  obtain ⟨u, hu, hune⟩ := g.U.bot_or_exists_ne_one.resolve_left (d.U_ne_bot g)
  have hKM : residualCommutator M t ≤ M := by
    rw [d.torus_eq_local_pair]
    exact inf_le_left.trans inf_le_left
  have hKC : residualCommutator M t ≤
      normalizer (centralizer (closure (Z ∩ (M : Set G)) : Set G) : Set G) :=
    hKM.trans ((normal_subgroupOf_iff_le_normalizer d.distinguished_centralizer_le).mp
      d.distinguished_centralizer_normal)
  have hKu : residualCommutator M t ≤ centralizer ({u} : Set G) :=
    (d.torus_centralizes_U g).trans (centralizer_le (Set.singleton_subset_iff.mpr hu))
  rw [← g.centralizer_U u hu hune]
  exact (le_inf hKC (hKu.trans (centralizer ({u} : Set G)).le_normalizer)).trans
    inf_normalizer_le_normalizer_inf

public theorem LocalGeometry.T_center_product (g : LocalGeometry Z M z t m) :
    (((center g.T).map g.T.subtype : Subgroup G) : Set G) =
      (closure (Z ∩ (M : Set G)) : Set G) * (g.U : Set G) := by
  rw [g.T_center]
  exact coe_mul_of_right_le_normalizer_left _ _
    ((le_centralizer_iff.mp (g.A_le_P.trans g.P_centralizes_U)).trans
      (Subgroup.centralizer_le_normalizer _))

public theorem LocalGeometry.T_card (g : LocalGeometry Z M z t m) :
    Nat.card g.T = (2 ^ (2 * m + 1)) ^ 2 * Nat.card g.U := by
  have hc := card_mul_eq_card_inf_mul_card_sup_of_normalizes
    (borelTwoCore M z t) g.U
    ((le_centralizer_iff.mp g.P_centralizes_U).trans (Subgroup.centralizer_le_normalizer _))
  rw [g.P_disjoint_U.eq_bot, Subgroup.card_bot, one_mul, ← g.T_eq_sup, g.P_card] at hc
  exact hc.symm

/-- The literal coset used in the first paragraph of GLS4, Chapter 2, Lemma 14.6. -/
@[expose] public def distinguishedCoset (Z : Set G) (M : Subgroup G) (u : G) : Set G :=
  {v : G | ∃ a ∈ closure (Z ∩ (M : Set G)), v = a * u}

/-- The pointwise kernel on Au is exactly T, for every nonidentity u in U. -/
public theorem LocalGeometry.distinguishedCoset_centralizer (g : LocalGeometry Z M z t m)
    {u : G} (hu : u ∈ g.U) (hune : u ≠ 1) :
    centralizer (distinguishedCoset Z M u) = g.T := by
  rw [← g.centralizer_U u hu hune]
  ext x
  have huΔ : u ∈ distinguishedCoset Z M u := ⟨1, one_mem _, (one_mul u).symm⟩
  constructor
  · intro hx
    have hux : u * x = x * u := hx u huΔ
    refine ⟨?_, mem_centralizer_singleton_iff.mpr hux.symm⟩
    intro a ha
    have haux : a * u ∈ centralizer ({x} : Set G) :=
      mem_centralizer_singleton_iff.mpr (hx (a * u) ⟨a, ha, rfl⟩)
    have hux' : u ∈ centralizer ({x} : Set G) := mem_centralizer_singleton_iff.mpr hux
    have hax := (centralizer ({x} : Set G)).mul_mem haux
      ((centralizer ({x} : Set G)).inv_mem hux')
    exact mem_centralizer_singleton_iff.mp (by simpa only [mul_inv_cancel_right] using hax)
  · rintro ⟨hxA, hxu⟩ v ⟨a, ha, rfl⟩
    have hux : u * x = x * u := (mem_centralizer_singleton_iff.mp hxu).symm
    calc
      a * u * x = a * (u * x) := mul_assoc _ _ _
      _ = a * (x * u) := by rw [hux]
      _ = x * (a * u) := by rw [← mul_assoc, hxA a ha, mul_assoc]

/-- Its set stabilizer normalizes its pointwise kernel, so lies in N_G(T). -/
public theorem LocalGeometry.distinguishedCoset_normalizer_le (g : LocalGeometry Z M z t m)
    {u : G} (hu : u ∈ g.U) (hune : u ≠ 1) :
    normalizer (distinguishedCoset Z M u) ≤ normalizer (g.T : Set G) := by
  have hn := (normal_subgroupOf_iff_le_normalizer
    (Subgroup.centralizer_le_normalizer (distinguishedCoset Z M u))).mp
    (normal_subgroupOf_centralizer_normalizer (distinguishedCoset Z M u))
  rwa [g.distinguishedCoset_centralizer hu hune] at hn

/-- This supplies the source's containment of the coset stabilizer in M. -/
public theorem Context.distinguishedCoset_normalizer_le_M (d : Context Z M z t m)
    (g : LocalGeometry Z M z t m) {u : G} (hu : u ∈ g.U) (hune : u ≠ 1) :
    normalizer (distinguishedCoset Z M u) ≤ M :=
  (g.distinguishedCoset_normalizer_le hu hune).trans (d.normalizer_T_le_M g)

/-- The global order has exactly one further factor q beyond the two-part of T. -/
public theorem Context.card_eq_q_mul_T_mul_odd (d : Context Z M z t m)
    (g : LocalGeometry Z M z t m) :
    ∃ c : ℕ, Odd c ∧ Nat.card G = 2 ^ (2 * m + 1) * Nat.card g.T * c := by
  let q := 2 ^ (2 * m + 1)
  let D := residualPairStabilizer M t
  obtain ⟨V, hV⟩ := g.U_sylow_pair
  have hD : Nat.card D = Nat.card g.U * (V : Subgroup D).index := by
    rw [← hV, card_map_of_injective D.subtype_injective]
    exact (V : Subgroup D).card_mul_index.symm
  have hi : Odd (V : Subgroup D).index :=
    Nat.not_even_iff_odd.mp (fun h => V.not_dvd_index h.two_dvd)
  have hq : Even q := even_two.pow_of_ne_zero (by omega : 2 * m + 1 ≠ 0)
  have hq2 : Even (q ^ 2) := hq.pow_of_ne_zero (by decide)
  have hpoly : Odd (q ^ 2 - q + 1) := by
    have he : q ^ 2 - q + 1 = 1 + (q - 1) * q := by
      simp only [Nat.sub_mul, one_mul, pow_two]
      omega
    rw [he]
    exact (hq.mul_left (q - 1)).one_add
  let c := (q ^ 2 - q + 1) * (V : Subgroup D).index *
    ((q ^ 2 + 1) * (q ^ 2 * (q - 1) + 1))
  refine ⟨c, (hpoly.mul hi).mul (hq2.add_one.mul (hq2.mul_right (q - 1)).add_one), ?_⟩
  calc
    Nat.card G = Nat.card M * Nat.card (G ⧸ M) := M.card_mul_index.symm
    _ = q * Nat.card g.T * c := by
      rw [d.card_pointStabilizer, d.degree, g.T_card]
      change q ^ 3 * (q ^ 2 - q + 1) * Nat.card D *
        ((q ^ 2 + 1) * (q ^ 2 * (q - 1) + 1)) = q * (q ^ 2 * Nat.card g.U) * c
      rw [hD]
      dsimp only [c]
      ring

/-- Once the translation quotient has order q, S is already Sylow in G. -/
public theorem Context.S_sylow_of_quotient_card (d : Context Z M z t m)
    (g : LocalGeometry Z M z t m)
    (hc : Nat.card (g.S ⧸ g.T.subgroupOf g.S) = 2 ^ (2 * m + 1)) :
    ∃ V : Sylow 2 G, (V : Subgroup G) = g.S := by
  have hS : Nat.card g.S = Nat.card g.T * 2 ^ (2 * m + 1) := by
    have hh := (g.T.subgroupOf g.S).card_mul_index
    rw [Nat.card_congr (subgroupOfEquivOfLe g.T_lt_S.le).toEquiv] at hh
    change Nat.card g.T * Nat.card (g.S ⧸ g.T.subgroupOf g.S) = Nat.card g.S at hh
    rw [hc] at hh
    exact hh.symm
  obtain ⟨c, hcodd, hcG⟩ := d.card_eq_q_mul_T_mul_odd g
  have hidx : g.S.index = c := by
    apply Nat.eq_of_mul_eq_mul_left (Nat.card_pos (α := g.S))
    rw [g.S.card_mul_index, hcG, hS]
    ring
  have hnot : ¬ 2 ∣ g.S.index := by
    rw [hidx]
    exact fun he => (Nat.not_even_iff_odd.mpr hcodd) (even_iff_two_dvd.mpr he)
  exact ⟨g.S_isPGroup.toSylow hnot, rfl⟩

/-- The literal quotient isomorphism supplies the missing ambient Sylow assertion. -/
public theorem Context.S_sylow_of_quotient_equiv (d : Context Z M z t m)
    (g : LocalGeometry Z M z t m)
    (he : letI := g.T_normal_in_S
      Nonempty ((g.S ⧸ g.T.subgroupOf g.S) ≃* closure (Z ∩ (M : Set G)))) :
    ∃ V : Sylow 2 G, (V : Subgroup G) = g.S := by
  let := g.T_normal_in_S
  obtain ⟨e⟩ := he
  exact d.S_sylow_of_quotient_card g
    ((Nat.card_congr e.toEquiv).trans d.distinguished_elementary_card.2)

public theorem Context.torus_conj_U (d : Context Z M z t m)
    (g : LocalGeometry Z M z t m) {k u : G}
    (hk : k ∈ residualCommutator M t) (hu : u ∈ g.U) : MulAut.conj k u = u := by
  change k * u * k⁻¹ = u
  rw [← d.torus_centralizes_U g hk u hu, mul_inv_cancel_right]

/-- The torus preserves every source coset Au before S-normality is known. -/
public theorem Context.torus_normalizes_distinguishedCoset (d : Context Z M z t m)
    (g : LocalGeometry Z M z t m) {u : G} (hu : u ∈ g.U) :
    residualCommutator M t ≤ normalizer (distinguishedCoset Z M u) := by
  have hstable (k : G) (hk : k ∈ residualCommutator M t)
      (v : G) (hv : v ∈ distinguishedCoset Z M u) :
      MulAut.conj k v ∈ distinguishedCoset Z M u := by
    obtain ⟨a, ha, rfl⟩ := hv
    exact ⟨MulAut.conj k a, (d.torus_le_normalizer_distinguished hk a).mp ha,
      by rw [map_mul, d.torus_conj_U g hk hu]⟩
  intro k hk
  apply mem_normalizer_iff_conj_image_eq.mpr
  apply Set.Subset.antisymm
  · rintro v ⟨w, hw, rfl⟩
    exact hstable k hk w hw
  · intro v hv
    refine ⟨MulAut.conj k⁻¹ v,
      hstable k⁻¹ ((residualCommutator M t).inv_mem hk) v hv, ?_⟩
    simp [MulAut.conj_apply, mul_assoc]

/-- This is the source's cyclic action on Delta minus its fixed point u. -/
public theorem Context.torus_regular_distinguishedCoset (d : Context Z M z t m)
    (g : LocalGeometry Z M z t m) (hsemi : TorusSemiregular M t)
    {u v w : G} (hu : u ∈ g.U)
    (hv : v ∈ distinguishedCoset Z M u) (hvu : v ≠ u)
    (hw : w ∈ distinguishedCoset Z M u) (hwu : w ≠ u) :
    ∃! k : residualCommutator M t, MulAut.conj (k : G) v = w := by
  obtain ⟨a, ha, rfl⟩ := hv
  obtain ⟨b, hb, rfl⟩ := hw
  have ha1 : a ≠ 1 := fun hh => hvu (by rw [hh, one_mul])
  have hb1 : b ≠ 1 := fun hh => hwu (by rw [hh, one_mul])
  obtain ⟨k, hk, huniq⟩ := d.torus_regular_distinguished g hsemi ha ha1 hb hb1
  refine ⟨k, ?_, ?_⟩
  · change MulAut.conj (k : G) (a * u) = b * u
    rw [map_mul, hk, d.torus_conj_U g k.property hu]
  · intro l hl
    apply huniq l
    rw [map_mul, d.torus_conj_U g l.property hu] at hl
    exact mul_right_cancel hl

public theorem Context.distinguishedCoset_card (d : Context Z M z t m) (u : G) :
    Nat.card (distinguishedCoset Z M u) = 2 ^ (2 * m + 1) := by
  let φ : closure (Z ∩ (M : Set G)) → distinguishedCoset Z M u :=
    fun a => ⟨a * u, a, a.property, rfl⟩
  have hφ : Function.Bijective φ := by
    constructor
    · intro a b hh
      exact Subtype.ext (mul_right_cancel (congrArg Subtype.val hh))
    · rintro ⟨v, a, ha, rfl⟩
      exact ⟨⟨a, ha⟩, rfl⟩
  exact (Nat.card_congr (Equiv.ofBijective φ hφ)).symm.trans
    d.distinguished_elementary_card.2

end BenderSuzuki.ZD.SuzukiExclusion
