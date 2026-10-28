module

public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.Generation.LinearRecognition.Centralizers.Counting.UniformCases.Numerics.Fibers.Pairs
public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.Generation.LinearRecognition.Centralizers.Counting.FixedPoints

/-!
# Odd-product pairs through fixed-coset incidence

Write Lᵥ for the distinguished centralizer closure and A for ⟨Z ∩ M⟩.
The involutions of Lᵥ are distinguished and form one local conjugacy class.
Each has a unique fixed coset, and Lᵥ is transitive on the cosets fixed by v.
The base point fiber is C_A(v) minus the identity, so the incidence count
is f(q-1), with q = |C_A(v)| and f the number of v-fixed cosets.

For a distinguished representative in the base fiber, products with
involutions outside that fiber have odd order. Products with the other
members of the same fiber have order two; the equal pair has product one.
Thus precisely q-2 partners are excluded. Local conjugacy transports this
count to every first factor, giving (q-1)f((f-1)(q-1)+1).

Only the distinguished subgroup is used for the exponent-two argument;
no exponent assumption on a full involution centralizer is needed. The
original z need not commute with v. The output supplies the odd-pair premise
of `proper_residualGenerated_fiber_counts_of_pair_counts` in `Fibers`.

Source: GLS4, Chapter 2, proof of Lemma 12.8,
`refs/KGroup/GLS4/Chapter2.tex`, lines 2155–2175.
-/

noncomputable section
namespace BenderSuzuki.ZD
open Subgroup Theory.GroupTheory PFAppendixIII PFchapter1section1
universe u
variable {G : Type u} [Group G] [Finite G] {Z : Set G} {M : Subgroup G}
namespace ResidualOddIncidence

private abbrev LocalInvolution (H : Type*) [Group H] := {x : H // orderOf x = 2}

private theorem inv_isInvolution {H : Type*} [Group H] (x : LocalInvolution H) :
    PFAppendixIII.IsInvolution x.val := (orderOf_eq_prime_iff.mp x.property).symm

private def conjInv {H : Type*} [Group H] (g : H) : LocalInvolution H ≃ LocalInvolution H :=
  (MulAut.conj g).toEquiv.subtypeEquiv (by
    intro x
    change orderOf x = 2 ↔ orderOf (MulAut.conj g x) = 2
    rw [(MulAut.conj g).orderOf_eq])

private theorem card_ne {T : Type*} [Finite T] (x : T) :
    Nat.card {y : T // y ≠ x} = Nat.card T - 1 := by
  classical
  let _ := Fintype.ofFinite T
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype_compl]
  simp [Nat.card_eq_fintype_card]

private theorem card_not {T : Type*} [Finite T] (p : T → Prop) :
    Nat.card {x : T // ¬ p x} = Nat.card T - Nat.card {x : T // p x} := by
  classical
  let _ := Fintype.ofFinite T
  simp only [Nat.card_eq_fintype_card, Fintype.card_subtype_compl]

private theorem card_incidence {I F : Type*} [Finite I] [Finite F]
    (R : I → F → Prop) (hu : ∀ x, ∃! b, R x b) (n : ℕ)
    (hc : ∀ b, Nat.card {x : I // R x b} = n) : Nat.card I = Nat.card F * n := by
  classical
  let _ := Fintype.ofFinite F
  let e : (Σ b : F, {x : I // R x b}) ≃ I := Equiv.ofBijective
    (fun p => p.2.val) (by
      constructor
      · rintro ⟨b, x, hx⟩ ⟨c, y, hy⟩ he
        change x = y at he
        subst y
        have hbc : b = c := (hu x).unique hx hy
        subst c
        rfl
      · intro x
        obtain ⟨b, hb, _⟩ := hu x
        exact ⟨⟨b, x, hb⟩, rfl⟩)
  rw [← Nat.card_congr e, Nat.card_sigma]
  simp [hc, Nat.card_eq_fintype_card]

omit [Finite G] in
private theorem base_fix_iff (x : G) :
    x • (QuotientGroup.mk 1 : G ⧸ M) = QuotientGroup.mk 1 ↔ x ∈ M := by
  change x ∈ MulAction.stabilizer G (QuotientGroup.mk 1 : G ⧸ M) ↔ _
  rw [baseCoset_stabilizer]

omit [Finite G] in
private theorem conj_fix_iff (g x : G) (b : G ⧸ M) :
    (g * x * g⁻¹) • (g • b) = g • b ↔ x • b = b := by
  simp only [mul_smul, inv_smul_smul, smul_left_cancel_iff]

private theorem base_involutions_card
    (h : IsProductDisconnected Z M) (r : SimpleReduction Z M)
    {t v : G} (htM : t ∉ M)
    (hvD : v ∈ residualPairStabilizer M t) (hv : PFAppendixIII.IsInvolution v)
    (hZ : Z ∩ (M : Set G) = (closure (Z ∩ (M : Set G)) : Set G) \ {1}) :
    Nat.card {x : LocalInvolution (centralizerClosure Z v) // ((x.val : centralizerClosure Z v) : G) ∈ M} =
      Nat.card (closure (Z ∩ (M : Set G)) ⊓ centralizer ({v} : Set G) : Subgroup G) - 1 := by
  let A := closure (Z ∩ (M : Set G)) ⊓ centralizer ({v} : Set G)
  let L := centralizerClosure Z v
  have hxZ (x : LocalInvolution L) : (x.val : G) ∈ Z :=
    (pair_involution_centralizerClosure_involutions h r htM hvD hv x.val.property).mp
      (IsInvolution.map_of_injective (inv_isInvolution x) L.subtype Subtype.val_injective)
  let e : {x : LocalInvolution L // (x.val : G) ∈ M} ≃ {a : A // a ≠ 1} := {
    toFun := fun x => ⟨⟨x.val.val, ⟨subset_closure ⟨hxZ x.val, x.property⟩,
      centralizerClosure_le Z v x.val.val.property⟩⟩,
      fun he => (inv_isInvolution x.val).ne_one (Subtype.ext (congrArg (fun a : A => (a : G)) he))⟩
    invFun := fun a => by
      have ha1 : (a.val : G) ≠ 1 := fun he => a.property (Subtype.ext he)
      have haZM : (a.val : G) ∈ Z ∩ (M : Set G) := by
        rw [hZ]
        exact ⟨a.val.property.1, ha1⟩
      have haL : (a.val : G) ∈ L := mem_centralizerClosure haZM.1
        (mem_centralizer_singleton_iff.mp a.val.property.2)
      refine ⟨⟨⟨a.val, haL⟩, ?_⟩, haZM.2⟩
      rw [← orderOf_coe]
      exact orderOf_eq_prime (h.involutions _ haZM.1).sq_eq_one ha1
    left_inv := fun x => rfl
    right_inv := fun a => rfl }
  exact (Nat.card_congr e).trans (card_ne (1 : A))

private theorem local_conjugator
    (h : IsProductDisconnected Z M) (r : SimpleReduction Z M)
    {t v : G} (htM : t ∉ M)
    (hvD : v ∈ residualPairStabilizer M t) (hv : PFAppendixIII.IsInvolution v)
    (w x : LocalInvolution (centralizerClosure Z v)) :
    ∃ g : centralizerClosure Z v, MulAut.conj g w.val = x.val := by
  obtain ⟨g, hg⟩ := (pair_involution_centralizerClosure_local h r htM hvD hv).2.2.involutions_conjugate
    (inv_isInvolution w) (inv_isInvolution x)
  exact ⟨g⁻¹, by simpa only [rightConjugateElem, MulAut.conj_apply, inv_inv] using hg⟩

private theorem local_involutions_card
    (h : IsProductDisconnected Z M) (r : SimpleReduction Z M)
    {z t v : G} (htM : t ∉ M)
    (hlocal : ResidualCentralizerLocalData Z M z t)
    (hvD : v ∈ residualPairStabilizer M t) (hv : PFAppendixIII.IsInvolution v)
    (hZ : Z ∩ (M : Set G) = (closure (Z ∩ (M : Set G)) : Set G) \ {1})
    (w : LocalInvolution (centralizerClosure Z v)) (hwZ : (w.val : G) ∈ Z) (hwM : (w.val : G) ∈ M) :
    Nat.card (LocalInvolution (centralizerClosure Z v)) =
      Nat.card {b : G ⧸ M // v • b = b} *
        (Nat.card (closure (Z ∩ (M : Set G)) ⊓ centralizer ({v} : Set G) : Subgroup G) - 1) := by
  let L := centralizerClosure Z v
  let F := {b : G ⧸ M // v • b = b}
  let alpha : G ⧸ M := QuotientGroup.mk 1
  have horbit := pair_involution_fixedPoints_eq_centralizerClosure_orbit r hlocal hvD hv
  apply card_incidence (fun (x : LocalInvolution L) (b : F) => (x.val : G) • b.val = b.val)
  · intro x
    obtain ⟨g, hg⟩ := local_conjugator h r htM hvD hv w x
    have hgG : (g : G) * (w.val : G) * (g : G)⁻¹ = (x.val : G) :=
      congrArg Subtype.val hg
    have hbeta : v • ((g : G) • alpha) = (g : G) • alpha := by
      apply Set.ext_iff.mp horbit _ |>.mpr
      exact MulAction.mem_orbit_iff.mpr ⟨g, rfl⟩
    refine ⟨⟨(g : G) • alpha, hbeta⟩, ?_, ?_⟩
    · change (x.val : G) • ((g : G) • alpha) = (g : G) • alpha
      rw [← hgG, conj_fix_iff]
      exact (base_fix_iff _).mpr hwM
    · intro b hb
      apply Subtype.ext
      have hwfix : (w.val : G) • ((g : G)⁻¹ • b.val) = (g : G)⁻¹ • b.val := by
        apply (conj_fix_iff (g : G) (w.val : G) ((g : G)⁻¹ • b.val)).mp
        simpa only [hgG, smul_inv_smul] using hb
      have he := action_fixedPoint_eq_base h hwZ hwM hwfix
      calc
        b.val = (g : G) • ((g : G)⁻¹ • b.val) := (smul_inv_smul _ _).symm
        _ = (g : G) • alpha := congrArg (fun b => (g : G) • b) he
  · intro b
    have hb : b.val ∈ MulAction.orbit L alpha :=
      (Set.ext_iff.mp horbit b.val).mp b.property
    obtain ⟨g, hg⟩ := MulAction.mem_orbit_iff.mp hb
    have e : {x : LocalInvolution L // (x.val : G) ∈ M} ≃
        {x : LocalInvolution L // (x.val : G) • b.val = b.val} :=
      (conjInv g).subtypeEquiv (by
        intro x
        change (x.val : G) ∈ M ↔
          ((g : G) * (x.val : G) * (g : G)⁻¹) • b.val = b.val
        change (g : G) • alpha = b.val at hg
        rw [← hg, conj_fix_iff]
        exact (base_fix_iff _).symm)
    exact (Nat.card_congr e).symm.trans (base_involutions_card h r htM hvD hv hZ)

private theorem partners_card_conj {H : Type*} [Group H]
    (w x : LocalInvolution H) (g : H) (hg : MulAut.conj g w.val = x.val) :
    Nat.card {y : LocalInvolution H // Odd (orderOf (x.val * y.val))} =
      Nat.card {y : LocalInvolution H // Odd (orderOf (w.val * y.val))} := by
  apply (Nat.card_congr ((conjInv g).subtypeEquiv ?_)).symm
  intro y
  change Odd (orderOf (w.val * y.val)) ↔
    Odd (orderOf (x.val * MulAut.conj g y.val))
  rw [← hg, ← map_mul, (MulAut.conj g).orderOf_eq]

private theorem base_not_odd_iff
    (h : IsProductDisconnected Z M) (r : SimpleReduction Z M)
    {t v : G} (htM : t ∉ M)
    (hvD : v ∈ residualPairStabilizer M t) (hv : PFAppendixIII.IsInvolution v)
    (hZ : Z ∩ (M : Set G) = (closure (Z ∩ (M : Set G)) : Set G) \ {1})
    (w : LocalInvolution (centralizerClosure Z v)) (hwZ : (w.val : G) ∈ Z) (hwM : (w.val : G) ∈ M)
    (s : LocalInvolution (centralizerClosure Z v)) :
    ¬ Odd (orderOf (w.val * s.val)) ↔ (s.val : G) ∈ M ∧ s ≠ w := by
  have hwI := inv_isInvolution w
  have hwG := IsInvolution.map_of_injective hwI (centralizerClosure Z v).subtype Subtype.val_injective
  have hsZ := (pair_involution_centralizerClosure_involutions h r htM hvD hv s.val.property).mp
    (IsInvolution.map_of_injective (inv_isInvolution s)
      (centralizerClosure Z v).subtype Subtype.val_injective)
  by_cases he : s = w
  · subst s
    have he1 : w.val * w.val = 1 := by simpa only [pow_two] using hwI.sq_eq_one
    simp [he1]
  by_cases hsM : (s.val : G) ∈ M
  · have hpA : (w.val : G) * (s.val : G) ∈ closure (Z ∩ (M : Set G)) :=
      mul_mem (subset_closure ⟨hwZ, hwM⟩) (subset_closure ⟨hsZ, hsM⟩)
    have hpne : (w.val : G) * (s.val : G) ≠ 1 := by
      intro hp
      apply he
      apply Subtype.ext
      apply Subtype.ext
      have hh := congrArg (fun y : G => (w.val : G) * y) hp
      have hww : (w.val : G) * (w.val : G) = 1 := by simpa only [pow_two, Subgroup.subtype_apply] using hwG.sq_eq_one
      simpa only [← mul_assoc, hww, one_mul, mul_one] using hh
    have hpZ : (w.val : G) * (s.val : G) ∈ Z := by
      have hp : (w.val : G) * (s.val : G) ∈ Z ∩ (M : Set G) := by
        rw [hZ]
        exact ⟨hpA, hpne⟩
      exact hp.1
    have ho : orderOf (w.val * s.val) = 2 := by
      rw [← orderOf_coe]
      exact orderOf_eq_prime (h.involutions _ hpZ).sq_eq_one hpne
    simp [ho, hsM, he]
  · have ho : Odd (orderOf (w.val * s.val)) := by
      rw [← orderOf_coe]
      exact productDisconnected_odd_orderOf_mul h hwZ hsZ hsM (Or.inl hwM)
    simp [ho, hsM]

private theorem base_partners_card
    (h : IsProductDisconnected Z M) (r : SimpleReduction Z M)
    {t v : G} (htM : t ∉ M)
    (hvD : v ∈ residualPairStabilizer M t) (hv : PFAppendixIII.IsInvolution v)
    (hZ : Z ∩ (M : Set G) = (closure (Z ∩ (M : Set G)) : Set G) \ {1})
    (w : LocalInvolution (centralizerClosure Z v)) (hwZ : (w.val : G) ∈ Z) (hwM : (w.val : G) ∈ M) :
    Nat.card {s : LocalInvolution (centralizerClosure Z v) // Odd (orderOf (w.val * s.val))} =
      Nat.card (LocalInvolution (centralizerClosure Z v)) -
        ((Nat.card (closure (Z ∩ (M : Set G)) ⊓ centralizer ({v} : Set G) : Subgroup G) - 1) - 1) := by
  let I := LocalInvolution (centralizerClosure Z v)
  let B := {x : I // (x.val : G) ∈ M}
  let wb : B := ⟨w, hwM⟩
  let e : {s : I // ¬ Odd (orderOf (w.val * s.val))} ≃ {s : B // s ≠ wb} := {
    toFun := fun s => ⟨⟨s.val, (base_not_odd_iff h r htM hvD hv hZ w hwZ hwM s.val).mp s.property |>.1⟩,
      fun he => ((base_not_odd_iff h r htM hvD hv hZ w hwZ hwM s.val).mp s.property).2
        (congrArg Subtype.val he)⟩
    invFun := fun s => ⟨s.val.val,
      (base_not_odd_iff h r htM hvD hv hZ w hwZ hwM s.val.val).mpr
        ⟨s.val.property, fun he => s.property (Subtype.ext he)⟩⟩
    left_inv := fun _ => rfl
    right_inv := fun _ => rfl }
  have hc := (Nat.card_congr e).trans (card_ne wb)
  have hbase := base_involutions_card h r htM hvD hv hZ
  change Nat.card B = _ at hbase
  rw [hbase] at hc
  have hc' := card_not (fun s : I => ¬ Odd (orderOf (w.val * s.val)))
  simpa only [not_not, hc] using hc'

private theorem odd_pairs_card_of_partners {v : G}
    (w : LocalInvolution (centralizerClosure Z v))
    (hconj : ∀ x : LocalInvolution (centralizerClosure Z v),
      ∃ g : centralizerClosure Z v, MulAut.conj g w.val = x.val) :
    Nat.card (ResidualCentralizerOddPairs Z v) =
      Nat.card (LocalInvolution (centralizerClosure Z v)) *
        Nat.card {s : LocalInvolution (centralizerClosure Z v) // Odd (orderOf (w.val * s.val))} := by
  classical
  let I := LocalInvolution (centralizerClosure Z v)
  let _ := Fintype.ofFinite I
  let e : ResidualCentralizerOddPairs Z v ≃
      (Σ x : I, {y : I // Odd (orderOf (x.val * y.val))}) := {
    toFun := fun p => ⟨⟨p.val.1, p.property.1⟩, ⟨p.val.2, p.property.2.1⟩, p.property.2.2⟩
    invFun := fun p => ⟨⟨p.1.val, p.2.val.val⟩, p.1.property, p.2.val.property, p.2.property⟩
    left_inv := fun _ => rfl
    right_inv := fun _ => rfl }
  have hc (x : I) : Nat.card {s : I // Odd (orderOf (x.val * s.val))} =
      Nat.card {s : I // Odd (orderOf (w.val * s.val))} := by
    obtain ⟨g, hg⟩ := hconj x
    exact partners_card_conj w x g hg
  rw [Nat.card_congr e, Nat.card_sigma]
  simp only [hc, Finset.sum_const, Finset.card_univ, smul_eq_mul]
  rw [← Nat.card_eq_fintype_card]

end ResidualOddIncidence
open ResidualOddIncidence in
/-- The actor's local odd-product pair count in GLS4, Chapter 2, Lemma 12.8.
Every involution has one fixed coset. Each point fiber has q-1 involutions,
and only its other q-2 members give even products. Equal pairs are included. -/
public theorem proper_residualGenerated_local_odd_pairs_card
    (h : MinimalCounterexample Z M) (r : SimpleReduction Z M)
    (ha : ResidualAction Z M) {z t v : G}
    (hz : z ∈ Z) (hzM : z ∈ M) (ht : t ∈ Z) (htM : t ∉ M)
    (hL : residualGenerated M z t ≠ ⊤)
    (heven : Even (Nat.card (residualPairStabilizer M t)))
    (hlocal : ResidualCentralizerLocalData Z M z t)
    (hvD : v ∈ residualPairStabilizer M t) (hv : PFAppendixIII.IsInvolution v) :
    let q := Nat.card (closure (Z ∩ (M : Set G)) ⊓ centralizer ({v} : Set G) : Subgroup G)
    let f := Nat.card {beta : G ⧸ M // v • beta = beta}
    Nat.card (ResidualCentralizerOddPairs Z v) =
      (q - 1) * f * ((f - 1) * (q - 1) + 1) := by
  obtain ⟨n, hn, hmodels, hAL, hDN, htrace, hcore, hnormal, hA, hcard, hZ, hrest⟩ :=
    proper_residualGenerated_structure h r ha hz hzM ht htM hL heven
  let L := centralizerClosure Z v
  obtain ⟨w0, hwM, hwI⟩ :=
    (pair_involution_centralizerClosure_local h.disconnected r htM hvD hv).2.2.exists_involution
  let w : LocalInvolution L := ⟨w0, orderOf_eq_prime hwI.sq_eq_one hwI.ne_one⟩
  have hwZ : (w.val : G) ∈ Z :=
    (pair_involution_centralizerClosure_involutions h.disconnected r htM hvD hv w.val.property).mp
      (IsInvolution.map_of_injective hwI L.subtype Subtype.val_injective)
  have htotal := local_involutions_card h.disconnected r htM hlocal hvD hv hZ w hwZ hwM
  have hpartners := base_partners_card h.disconnected r htM hvD hv hZ w hwZ hwM
  have hpairs := odd_pairs_card_of_partners w
    (local_conjugator h.disconnected r htM hvD hv w)
  rw [hpairs, hpartners, htotal]
  dsimp only
  let q := Nat.card (closure (Z ∩ (M : Set G)) ⊓ centralizer ({v} : Set G) : Subgroup G)
  let f := Nat.card {beta : G ⧸ M // v • beta = beta}
  change f * (q - 1) * (f * (q - 1) - (q - 1 - 1)) =
    (q - 1) * f * ((f - 1) * (q - 1) + 1)
  have hf : 1 ≤ f := by
    let b : {beta : G ⧸ M // v • beta = beta} :=
      ⟨QuotientGroup.mk 1, (base_fix_iff v).mpr hvD.1⟩
    let _ : Nonempty {beta : G ⧸ M // v • beta = beta} := ⟨b⟩
    exact Nat.card_pos
  have hq : 1 ≤ q - 1 := by
    let _ : Nonempty {x : LocalInvolution L // (x.val : G) ∈ M} := ⟨⟨w, hwM⟩⟩
    have hc := Nat.card_pos (α := {x : LocalInvolution L // (x.val : G) ∈ M})
    rw [base_involutions_card h.disconnected r htM hvD hv hZ] at hc
    exact hc
  have he : f * (q - 1) - (q - 1 - 1) = (f - 1) * (q - 1) + 1 := by
    have hf' : f = (f - 1) + 1 := by omega
    rw [hf', Nat.add_mul, one_mul, Nat.add_sub_cancel]
    omega
  rw [he, Nat.mul_comm f (q - 1)]

end BenderSuzuki.ZD
