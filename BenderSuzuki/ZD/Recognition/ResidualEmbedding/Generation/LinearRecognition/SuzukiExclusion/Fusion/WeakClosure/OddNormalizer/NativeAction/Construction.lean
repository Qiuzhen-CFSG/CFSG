module

public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.Generation.LinearRecognition.SuzukiExclusion.Fusion.WeakClosure.OddNormalizer.ActionContract
public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.Generation.LinearRecognition.SuzukiExclusion.Fusion.ZStarDescent.Normalizer
public import Theory.GroupTheory.PGroup.FrattiniAutomorphismKernel

/-!
# Conjugation and its kernel for the Suzuki odd normalizer

Conjugation on the literal image of S in M/M° factors through N_M(S)/S
when that image is elementary abelian. Its kernel is exactly S: the
U-orbits put M° in [S,S], and the Burnside basis-kernel theorem makes the
kernel a two-group. The centralizer of S is contained in T, so Sylow
maximality completes the kernel argument. The same inclusions identify
the cyclic image of K and preserve its order q−1.

This constructs the action, faithfulness, odd order, and torus order used
in GLS4, Chapter 2, Lemma 14.9, refs/KGroup/GLS4/Chapter2.tex, lines
2600–2615. The two torus-centralizer clauses of ActionData remain separate.
-/

noncomputable section
namespace BenderSuzuki.ZD.SuzukiExclusion.OddNormalizer
open Subgroup
open scoped IsMulCommutative
variable {G : Type*} [Group G] [Finite G] {Z : Set G} {M : Subgroup G}
  {z t : G} {m : ℕ}

/-- Conjugation by the actual normalizer on the image in M/M°. -/
@[expose] public def normalizerAction (d : Context Z M z t m) (g : LocalGeometry Z M z t m) :
    normalizerInM g →* MulAut (sylowImage d g) :=
  (sylowImage d g).normalizerMonoidHom.comp
    ((pointProjection d).comp (normalizerInM g).subtype |>.codRestrict
      (normalizer (sylowImage d g : Set (pointQuotient d))) (by
        intro n
        have h := mem_map_of_mem (pointProjection d) n.property
        have he := d.quotient_sylow_normalizer g
        change (normalizerInM g).map (pointProjection d) =
          normalizer (sylowImage d g : Set (pointQuotient d)) at he
        exact he ▸ h))

public theorem normalizerAction_apply (d : Context Z M z t m) (g : LocalGeometry Z M z t m)
    (n : normalizerInM g) (v : sylowImage d g) :
    (normalizerAction d g n v : pointQuotient d) =
      pointProjection d (n : M) * (v : pointQuotient d) * (pointProjection d (n : M))⁻¹ := rfl

public theorem sylow_le_normalizerAction_ker (d : Context Z M z t m) (g : LocalGeometry Z M z t m)
    (he : ElementaryQuotient d g) :
    (g.S.subgroupOf M).subgroupOf (normalizerInM g) ≤ (normalizerAction d g).ker := by
  let : IsElementaryAbelian 2 (sylowImage d g) := he
  intro n hn
  apply MulEquiv.ext
  intro v
  apply Subtype.ext
  rw [normalizerAction_apply]
  have hnv : Commute (⟨pointProjection d (n : M), mem_map_of_mem _ hn⟩ : sylowImage d g) v :=
    Commute.all _ _
  have hc := congrArg Subtype.val hnv.eq
  change pointProjection d (n : M) * (v : pointQuotient d) =
    (v : pointQuotient d) * pointProjection d (n : M) at hc
  rw [hc, mul_inv_cancel_right]
  rfl

/-- The actual quotient actor acts by conjugation. -/
@[expose] public def nativeAction (d : Context Z M z t m) (g : LocalGeometry Z M z t m)
    (he : ElementaryQuotient d g) : quotient g →* MulAut (sylowImage d g) :=
  QuotientGroup.lift _ (normalizerAction d g) (sylow_le_normalizerAction_ker d g he)

public theorem nativeAction_conjugation (d : Context Z M z t m) (g : LocalGeometry Z M z t m)
    (he : ElementaryQuotient d g) (n : normalizerInM g) (v : sylowImage d g) :
    (nativeAction d g he (projection g n) v : pointQuotient d) =
      pointProjection d (n : M) * (v : pointQuotient d) * (pointProjection d (n : M))⁻¹ := rfl

public theorem quotient_odd (g : LocalGeometry Z M z t m) (s : SylowGeometry g) :
    Odd (Nat.card (quotient g)) := by
  obtain ⟨V, hV⟩ := s.S_sylow
  let W := V.subtype (show (V : Subgroup G) ≤ M by rw [hV]; exact g.S_le_M)
  let P := W.subtype (show (W : Subgroup M) ≤ normalizerInM g by
    change (V : Subgroup G).subgroupOf M ≤ normalizerInM g
    rw [hV]
    exact (g.S.subgroupOf M).le_normalizer)
  have hP : (P : Subgroup (normalizerInM g)) =
      (g.S.subgroupOf M).subgroupOf (normalizerInM g) := by
    simp only [P, W, Sylow.coe_subtype, hV]
  apply Nat.not_even_iff_odd.mp
  intro h
  apply P.not_dvd_index
  rw [hP]
  exact even_iff_two_dvd.mp h

private theorem torus_le_M (d : Context Z M z t m) : residualCommutator M t ≤ M := by
  rw [d.torus_eq_local_pair]
  exact inf_le_left.trans inf_le_left

private theorem torus_le_N (d : Context Z M z t m) (g : LocalGeometry Z M z t m)
    (s : SylowGeometry g) : (residualCommutator M t).subgroupOf M ≤ normalizerInM g := by
  intro k hk
  exact le_normalizer_comap M.subtype (d.torus_le_normalizer_S g s hk)

private def torusEquiv (d : Context Z M z t m) (g : LocalGeometry Z M z t m)
    (s : SylowGeometry g) :
    (((residualCommutator M t).subgroupOf M).subgroupOf (normalizerInM g)) ≃*
      residualCommutator M t :=
  (subgroupOfEquivOfLe (torus_le_N d g s)).trans (subgroupOfEquivOfLe (torus_le_M d))

public theorem torusImage_cyclic (d : Context Z M z t m) (g : LocalGeometry Z M z t m)
    (s : SylowGeometry g) : IsCyclic (torusImage g) := by
  let e := torusEquiv d g s
  let := d.torus_cyclic
  let : IsCyclic (((residualCommutator M t).subgroupOf M).subgroupOf (normalizerInM g)) :=
    isCyclic_of_surjective e.symm.toMonoidHom e.symm.surjective
  exact isCyclic_of_surjective ((projection g).subgroupMap _) ((projection g).subgroupMap_surjective _)

public theorem torusImage_card (d : Context Z M z t m) (g : LocalGeometry Z M z t m)
    (s : SylowGeometry g) : Nat.card (torusImage g) = 2 ^ (2 * m + 1) - 1 := by
  let K := ((residualCommutator M t).subgroupOf M).subgroupOf (normalizerInM g)
  have hS : IsPGroup 2 g.S := by
    obtain ⟨V, hV⟩ := s.S_sylow
    exact hV ▸ V.isPGroup'
  have hodd : Odd (Nat.card (residualCommutator M t)) := by
    rw [d.torus_card]
    exact Nat.Even.sub_odd Nat.one_le_two_pow
      (Even.pow_of_ne_zero even_two (by omega : 2 * m + 1 ≠ 0)) odd_one
  have hd : Disjoint g.S (residualCommutator M t) := by
    obtain ⟨i, hi⟩ := hS.exists_card_eq
    apply disjoint_of_coprime_natCard
    rw [hi]
    exact hodd.coprime_two_left.pow_left i
  have hk : ((projection g).subgroupMap K).ker = ⊥ := by
    apply bot_unique
    intro k hk
    have hh : projection g (k : normalizerInM g) = 1 := congrArg Subtype.val hk
    have hS : (k : normalizerInM g) ∈
        (g.S.subgroupOf M).subgroupOf (normalizerInM g) :=
      (QuotientGroup.eq_one_iff _).mp hh
    exact Subtype.ext (Subtype.ext (Subtype.ext (hd.le_bot ⟨hS, k.property⟩)))
  let e := MulEquiv.ofBijective ((projection g).subgroupMap K)
    ⟨(MonoidHom.ker_eq_bot_iff _).mp hk, (projection g).subgroupMap_surjective K⟩
  exact (Nat.card_congr e.toEquiv).symm.trans
    ((Nat.card_congr (torusEquiv d g s).toEquiv).trans d.torus_card)

/-- The full centralizer of S lies in S, using the literal subgroup M°U. -/
public theorem sylow_selfCentralizing (g : LocalGeometry Z M z t m)
    (hU : Nat.card g.U = 2) : centralizer (g.S : Set G) ≤ g.S := by
  have hAU : closure (Z ∩ (M : Set G)) ⊔ g.U ≤ g.S :=
    sup_le g.closure_le_S g.U_le_S
  have h := centralizer_le hAU
  rw [ZStarDescent.centralizer_AU g hU] at h
  exact h.trans g.T_lt_S.le

/-- The kernel before passage to N/S is precisely S. The Frattini kernel
argument uses M° ≤ [S,S], obtained from the actual U-orbits. -/
public theorem normalizerAction_ker (d : Context Z M z t m) (g : LocalGeometry Z M z t m)
    (s : SylowGeometry g) (hU : Nat.card g.U = 2) (he : ElementaryQuotient d g) :
    (normalizerAction d g).ker = (g.S.subgroupOf M).subgroupOf (normalizerInM g) := by
  let : ((closure (Z ∩ (M : Set G))).subgroupOf M).Normal :=
    distinguishedClosure_normal d.minimal.disconnected
  let N := normalizerInM g
  let P := (g.S.subgroupOf M).subgroupOf N
  have hS : IsPGroup 2 g.S := by
    obtain ⟨V, hV⟩ := s.S_sylow
    exact hV ▸ V.isPGroup'
  let : Fact (IsPGroup 2 g.S) := ⟨hS⟩
  let e : P ≃* g.S :=
    (subgroupOfEquivOfLe (g.S.subgroupOf M).le_normalizer).trans
      (subgroupOfEquivOfLe g.S_le_M)
  have hP : IsPGroup 2 P := hS.comap_subtype.comap_subtype
  let a : N →* MulAut P := MulAut.conjNormal
  have ha : IsPGroup 2 a.ker := by
    apply hP.to_le
    intro x hx
    apply sylow_selfCentralizing g hU
    apply mem_centralizer_iff.mpr
    intro y hy
    let yP := e.symm ⟨y, hy⟩
    have hh := congrArg (fun b : MulAut P => (((b yP : N) : M) : G)) hx
    change ((x : M) : G) * y * ((x : M) : G)⁻¹ = y at hh
    exact (mul_inv_eq_iff_eq_mul.mp hh).symm
  let b := (quotientAut (frattini P)).comp a
  have hb : IsPGroup 2 b.ker :=
    (isPGroup_quotientAut_frattini_kernel hP).comap_of_ker_isPGroup a ha
  have hker : (normalizerAction d g).ker ≤ b.ker := by
    intro x hx
    apply MulEquiv.ext
    intro q
    obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective (frattini P) q
    change quotientAut (frattini P) (a x) (QuotientGroup.mk' (frattini P) y) =
      QuotientGroup.mk' (frattini P) y
    rw [quotientAut_apply_mk]
    apply QuotientGroup.eq.mpr
    let v : sylowImage d g :=
      ⟨pointProjection d ((y : N) : M), mem_map_of_mem _ y.property⟩
    have hv := congrArg (fun c : MulAut (sylowImage d g) =>
      (c v : pointQuotient d)) hx
    change (normalizerAction d g x v : pointQuotient d) = v at hv
    rw [normalizerAction_apply] at hv
    have hdiff : pointProjection d
        (((y : N) : M)⁻¹ * ((x : M) * ((y : N) : M) * (x : M)⁻¹)) = 1 := by
      simp only [map_mul, map_inv]
      change (pointProjection d ((y : N) : M))⁻¹ *
        (pointProjection d (x : M) * pointProjection d ((y : N) : M) *
          (pointProjection d (x : M))⁻¹) = 1
      rw [show pointProjection d (x : M) * pointProjection d ((y : N) : M) *
        (pointProjection d (x : M))⁻¹ = pointProjection d ((y : N) : M) from hv]
      exact inv_mul_cancel _
    have hA : (((y : N) : M)⁻¹ * ((x : M) * ((y : N) : M) * (x : M)⁻¹) : M) ∈
        (closure (Z ∩ (M : Set G))).subgroupOf M :=
      (QuotientGroup.eq_one_iff _).mp hdiff
    obtain ⟨w, hw, hwv⟩ := ZStarDescent.distinguishedClosure_le_S_commutator g s hU hA
    have hwPhi := commutator_le_frattini_of_isPGroup (p := 2) hw
    have hePhi := frattini_le_comap_frattini_of_surjective
      (φ := e.symm.toMonoidHom) e.symm.surjective hwPhi
    have hew : e.symm w = y⁻¹ * a x y := by
      apply Subtype.ext
      apply Subtype.ext
      apply Subtype.ext
      exact hwv
    change e.symm w ∈ frattini P at hePhi
    rw [hew] at hePhi
    simpa only [mul_inv_rev, inv_inv] using (frattini P).inv_mem hePhi
  have hkP := hb.to_le hker
  obtain ⟨V, hV⟩ := s.S_sylow
  let W := V.subtype (show (V : Subgroup G) ≤ M by rw [hV]; exact g.S_le_M)
  let Q := W.subtype (show (W : Subgroup M) ≤ N by
    change (V : Subgroup G).subgroupOf M ≤ N
    rw [hV]
    exact (g.S.subgroupOf M).le_normalizer)
  have hQ : (Q : Subgroup N) = P := by simp only [Q, W, Sylow.coe_subtype, hV, P]
  have hle := sylow_le_normalizerAction_ker d g he
  exact (Q.is_maximal' hkP (by rwa [hQ])).trans hQ

/-- Faithfulness of the literal N_M(S)/S action, with no extra kernel premise. -/
public theorem nativeAction_faithful (d : Context Z M z t m) (g : LocalGeometry Z M z t m)
    (s : SylowGeometry g) (hU : Nat.card g.U = 2) (he : ElementaryQuotient d g) :
    Function.Injective (nativeAction d g he) := by
  apply (QuotientGroup.injective_lift_iff _ _ _).mpr
  exact (normalizerAction_ker d g s hU he).symm

end BenderSuzuki.ZD.SuzukiExclusion.OddNormalizer
