module

public import Theory.GroupTheory.CyclicSylowOuterKernel
public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.LocalResidual.NormalComplements
public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.LocalResidual.NormalComplements.RankOne.LocalRecognition.Source.Basic
public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.LocalResidual.NormalComplements.RankOne.Selection
public import BenderSuzuki.ZD.RankOne

/-!
# The outer-action step in Corollary 16.6(e)

For the marked involution u, write B = C_G(u) and L = B°. The actual
outer action of B/L on L, together with the order-two Sylow subgroup of
C_B(L), proves cyclicity of Sylow two-subgroups in Y ∩ B whenever Y° = 1.
Every involution of L is distinguished, so Y ∩ L is odd. The four-group
conclusion of 16.6(d) excludes elementary fours in Y; Z* then gives
Y = O₂′(Y) C_Y(u). Passing through that odd quotient proves cyclicity
of Sylow two-subgroups of Y, and Burnside transfer gives a normal
complement. Conjugacy supplies the marked element when Y is even.

Source: GLS IV, Chapter 2, the final paragraph of Corollary 16.6(e).
The earlier centralizer-size, outer-model and involution-fusion conclusions
remain explicit source premises; the outer-action kernel and odd-intersection
steps are proved here on the literal internal local circle.
-/

noncomputable section
namespace BenderSuzuki.ZD
open Theory.GroupTheory PFchapter1section1 PFAppendixII PFAppendixIII
open Subgroup
variable {G : Type*} [Group G] [Finite G] {Z : Set G} {M : Subgroup G}

omit [Finite G] in
private theorem circle_bot_not_mem (h : IsProductDisconnected Z M)
    (Y : Subgroup G) (hY : localCircle Z Y = ⊥) {y : G} (hy : y ∈ Y) : y ∉ Z := by
  intro hz
  have hm : (⟨y, hy⟩ : Y) ∈ localCircle Z Y := subset_closure hz
  rw [hY] at hm
  exact (h.involutions y hz).ne_one (congrArg Subtype.val (mem_bot.mp hm))

omit [Finite G] in
private theorem four_free_of_circle_bot (h : IsProductDisconnected Z M)
    (hfour : ∀ E : Subgroup G, Nat.card E = 4 → (∀ x : E, x ^ 2 = 1) →
      ∃ z ∈ E, z ∈ Z)
    (Y : Subgroup G) (hY : localCircle Z Y = ⊥) : ¬ TwoRankAtLeastTwo Y := by
  rintro ⟨E, hc, hs⟩
  obtain ⟨z, hz, hzZ⟩ := hfour (E.map Y.subtype)
    (by simpa only [card_map_of_injective Y.subtype_injective] using hc) (by
      rintro ⟨x, y, hy, rfl⟩
      exact Subtype.ext (congrArg (fun a : E => ((a : Y) : G)) (hs ⟨y, hy⟩)))
  obtain ⟨y, _, rfl⟩ := hz
  exact circle_bot_not_mem h Y hY y.property hzZ

private theorem no_elementary_four_of_injective
    {A D : Type*} [Group A] [Group D]
    (f : A →* D) (hf : Function.Injective f) (hr : ¬ TwoRankAtLeastTwo D) :
    ∀ V : Subgroup A, IsElementaryAbelian 2 V → Nat.card V ≠ 4 := by
  intro V hV hc
  let := hV
  apply hr
  refine ⟨V.map f, by simpa only [card_map_of_injective hf] using hc, ?_⟩
  rintro ⟨x, y, hy, rfl⟩
  apply Subtype.ext
  simpa only [MonoidHom.comp_apply, Subgroup.subtype_apply, Subgroup.coe_pow, Subgroup.coe_one, map_pow, map_one] using congrArg (f.comp V.subtype)
    (Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
      (IsElementaryAbelian.exponent_dvd_p 2 V) (⟨y, hy⟩ : V))

private theorem circle_intersection_odd (h : IsProductDisconnected Z M)
    (r : SimpleReduction Z M) (B Y : Subgroup G) (hB : B ≠ ⊤)
    (hBM : ¬ B ≤ M) (hne : ∃ z ∈ Z, z ∈ B ∧ z ∈ M)
    (hY : localCircle Z Y = ⊥) :
    Odd (Nat.card ((localCircle Z B).subgroupOf (Y.subgroupOf B))) := by
  apply Nat.coprime_two_left.mp
  apply Nat.prime_two.coprime_iff_not_dvd.mpr
  intro hd
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' 2 hd
  have hi : IsInvolution x := ⟨(orderOf_eq_prime_iff.mp hx).2,
    (orderOf_eq_prime_iff.mp hx).1⟩
  let f : (localCircle Z B).subgroupOf (Y.subgroupOf B) →* localCircle Z B :=
    { toFun := fun a => ⟨a.val.val, a.property⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl }
  have hf : Function.Injective f := by
    intro a b he
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun z : localCircle Z B => z.val) he
  have hz := localCircle_involution_mem h r B hB hBM hne
    (IsInvolution.map_of_injective hi f hf)
  exact circle_bot_not_mem h Y hY x.val.property hz

private def centralizer_intersection_equiv (Y : Subgroup G) {u : G} (hu : u ∈ Y) :
    centralizer ({(⟨u, hu⟩ : Y)} : Set Y) ≃*
      Y.subgroupOf (centralizer ({u} : Set G)) where
  toFun x := ⟨⟨x.val.val, mem_centralizer_singleton_iff.mpr
    (congrArg Subtype.val (mem_centralizer_singleton_iff.mp x.property))⟩,
      x.val.property⟩
  invFun x := ⟨⟨x.val.val, x.property⟩, mem_centralizer_singleton_iff.mpr
    (Subtype.ext (mem_centralizer_singleton_iff.mp x.val.property))⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl

private theorem cyclic_sylow_of_equiv {A D : Type*} [Group A] [Group D]
    [Finite A] [Finite D] (e : A ≃* D) (hD : ∀ S : Sylow 2 D, IsCyclic S)
    (P : Sylow 2 A) : IsCyclic P := by
  let Q : Sylow 2 D := P.mapSurjective (f := e.toMonoidHom) e.surjective
  let : IsCyclic ((P : Subgroup A).map e.toMonoidHom) := hD Q
  exact isCyclic_of_injective (e.toMonoidHom.subgroupMap (P : Subgroup A))
    (fun _ _ he => Subtype.ext (e.injective (congrArg Subtype.val he)))

/-- The literal marked-element form of 16.6(e). Oddness of the local-circle
intersection is deduced from local strong embedding, and the Z* factorization
is applied to Y itself. -/
public theorem local_cyclicSylow_of_marked_outer
    (h : IsProductDisconnected Z M) (r : SimpleReduction Z M)
    {u : G} (hu : IsInvolution u)
    (hBM : ¬ centralizer ({u} : Set G) ≤ M)
    (hne : ∃ z ∈ Z, z ∈ centralizer ({u} : Set G) ∧ z ∈ M)
    (hfour : ∀ E : Subgroup G, Nat.card E = 4 → (∀ x : E, x ^ 2 = 1) →
      ∃ z ∈ E, z ∈ Z)
    (hJ : ∀ S : Sylow 2 (centralizer
      (localCircle Z (centralizer ({u} : Set G)) : Set (centralizer ({u} : Set G)))),
      Nat.card S ≤ 2)
    (hOuter : ∀ S : Sylow 2 (MulAut.Outer
      (localCircle Z (centralizer ({u} : Set G)))), IsCyclic S)
    (Y : Subgroup G) (hY : localCircle Z Y = ⊥) (huY : u ∈ Y)
    (P : Sylow 2 Y) : IsCyclic P := by
  let B := centralizer ({u} : Set G)
  let L := localCircle Z B
  let H := Y.subgroupOf B
  let : L.Normal := localCircle_normal h B hBM hne
  have hr := four_free_of_circle_bot h hfour Y hY
  have hodd := circle_intersection_odd h r B Y
    (r.involution_centralizer_ne_top h hu) hBM hne hY
  let f : H →* Y :=
    { toFun := fun x => ⟨x.val.val, x.property⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl }
  have hf : Function.Injective f := by
    intro x y he
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun z : Y => z.val) he
  have hH : ∀ S : Sylow 2 H, IsCyclic S :=
    Subgroup.sylow_cyclic_of_odd_intersection_cyclic_outer L H hodd hJ hOuter
      (no_elementary_four_of_injective f hf hr)
  have hC : ∀ S : Sylow 2 (centralizer ({(⟨u, huY⟩ : Y)} : Set Y)), IsCyclic S :=
    cyclic_sylow_of_equiv (centralizer_intersection_equiv Y huY) hH
  exact P.isCyclic_of_odd_normal_supplement (pPrimeCore 2 Y) _
    (Nat.coprime_two_left.mp pPrimeCore_coprime_card)
    (pPrimeCore_sup_centralizer_eq_top_of_not_twoRank hr (IsInvolution.subtype hu huY)) hC

/-- Corollary 16.6(e), with the earlier four-group, fusion and outer-model
conclusions as explicit inputs. The marked involution need not belong to Y:
fusion conjugates an involution of each even Y to the marked one. -/
public theorem local_normalComplement_cyclicSylow_of_marked_outer
    (h : IsProductDisconnected Z M) (r : SimpleReduction Z M)
    {u : G} (hu : IsInvolution u)
    (hBM : ¬ centralizer ({u} : Set G) ≤ M)
    (hne : ∃ z ∈ Z, z ∈ centralizer ({u} : Set G) ∧ z ∈ M)
    (hfour : ∀ E : Subgroup G, Nat.card E = 4 → (∀ x : E, x ^ 2 = 1) →
      ∃ z ∈ E, z ∈ Z)
    (hclasses : ∀ v : G, IsInvolution v → v ∈ Z ∨ IsConj u v)
    (hJ : ∀ S : Sylow 2 (centralizer
      (localCircle Z (centralizer ({u} : Set G)) : Set (centralizer ({u} : Set G)))),
      Nat.card S ≤ 2)
    (hOuter : ∀ S : Sylow 2 (MulAut.Outer
      (localCircle Z (centralizer ({u} : Set G)))), IsCyclic S)
    (Y : Subgroup G) (hY : localCircle Z Y = ⊥) :
    HasNormalPComplement 2 Y ∧ ∀ P : Sylow 2 Y, IsCyclic P := by
  have hcyc : ∀ P : Sylow 2 Y, IsCyclic P := by
    by_cases heven : 2 ∣ Nat.card Y
    · obtain ⟨v, hv⟩ := exists_prime_orderOf_dvd_card' 2 heven
      have hvi : IsInvolution v := ⟨(orderOf_eq_prime_iff.mp hv).2,
        (orderOf_eq_prime_iff.mp hv).1⟩
      have hvg : IsInvolution (v : G) :=
        IsInvolution.map_of_injective hvi Y.subtype Y.subtype_injective
      have hconj := (hclasses v hvg).resolve_left (circle_bot_not_mem h Y hY v.property)
      obtain ⟨g, hg⟩ := isConj_iff.mp hconj
      let e := MulAut.conj g⁻¹
      let Y' := Y.map e.toMonoidHom
      have hg' : e v = u := by
        rw [← hg]
        simp [e, mul_assoc]
      have huY' : u ∈ Y' := ⟨v, v.property, hg'⟩
      have hY' : localCircle Z Y' = ⊥ := by
        apply le_antisymm ?_ bot_le
        rw [localCircle, closure_le]
        intro x hx
        obtain ⟨y, hy, he⟩ := x.property
        have hz : e y ∈ Z := by
          change (x : G) ∈ Z at hx
          change e y = (x : G) at he
          exact he.symm ▸ hx
        have hyZ : y ∈ Z := by
          have hh := h.invariant g (e y) hz
          simpa [e, MulAut.conj_apply, mul_assoc] using hh
        exact False.elim (circle_bot_not_mem h Y hY hy hyZ)
      exact cyclic_sylow_of_equiv (e.subgroupMap Y)
        (local_cyclicSylow_of_marked_outer h r hu hBM hne hfour hJ hOuter Y' hY' huY')
    · intro P
      have hc : Nat.card P = 1 := P.isPGroup'.card_eq_or_dvd.resolve_right
        (fun hd => heven (hd.trans (card_subgroup_dvd_card (P : Subgroup Y))))
      let : Subsingleton P := (Nat.card_eq_one_iff_unique.mp hc).1
      infer_instance
  exact ⟨local_normalComplement_of_cyclicSylow Y hcyc, hcyc⟩

/-- The source endpoint applied to the actual two-point stabilizer inside M.
Product disconnection supplies its trivial circle, and the residual action
supplies evenness; no cyclic-Sylow premise is added at this consumer. -/
public theorem residualPairIn_normalComplement_cyclicSylow_of_marked_outer
    (h : IsProductDisconnected Z M) (r : SimpleReduction Z M)
    (ha : ResidualAction Z M) (hn : ¬ IsStronglyEmbedded M)
    {u : G} (hu : IsInvolution u)
    (hBM : ¬ centralizer ({u} : Set G) ≤ M)
    (hne : ∃ z ∈ Z, z ∈ centralizer ({u} : Set G) ∧ z ∈ M)
    (hfour : ∀ E : Subgroup G, Nat.card E = 4 → (∀ x : E, x ^ 2 = 1) →
      ∃ z ∈ E, z ∈ Z)
    (hclasses : ∀ v : G, IsInvolution v → v ∈ Z ∨ IsConj u v)
    (hJ : ∀ S : Sylow 2 (centralizer
      (localCircle Z (centralizer ({u} : Set G)) : Set (centralizer ({u} : Set G)))),
      Nat.card S ≤ 2)
    (hOuter : ∀ S : Sylow 2 (MulAut.Outer
      (localCircle Z (centralizer ({u} : Set G)))), IsCyclic S)
    {t : G} (ht : t ∉ M) :
    HasNormalPComplement 2 (residualPairIn M t) ∧
      2 ∣ Nat.card (residualPairIn M t) ∧
      ∀ S : Sylow 2 (residualPairIn M t), IsCyclic S := by
  have hlocal := local_normalComplement_cyclicSylow_of_marked_outer
    h r hu hBM hne hfour hclasses hJ hOuter (residualPairStabilizer M t)
      (residualPairStabilizer_localClosure_eq_bot h ht)
  have hcyc := cyclic_sylow_of_equiv (residualPairInEquiv M t) hlocal.2
  exact ⟨local_normalComplement_of_cyclicSylow _ hcyc,
    residualPairIn_even h ha hn ht, hcyc⟩

end BenderSuzuki.ZD
