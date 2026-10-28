module
public import CFSG.Quasithin.Chapter2.Section04.LinearShadows.Single.FieldInvolutionCoreSource
public import CFSG.Quasithin.Chapter2.Section04.LinearShadows.Single.DistinguishedGeometrySource
public import CFSG.Quasithin.Chapter2.Section04.LinearShadows.Single.LinearFixedFusionSource

/-!
# The original field involution cannot fuse to a full-center fixed row

The exact conjugation equalizer on the two-core is the literal ambient
centralizer intersection. The source fixed-square theorem therefore gives
its order directly; in the centerless block, this order is 2^n. Applying
the TI elementary-pair obstruction discharges both the fixed-plane count
and TI premises in the full-center fusion branch on printed p.539.

The actual Sylow centralizer and involution closure remain the source
2.4.23(4) and 2.4.21 inputs. The final theorem applies the count to the
original marked field involution, with its original embeddings.
Source: Aschbacher–Smith, Lemma 2.4.12(2) and printed p.539.
-/

public section
open Subgroup
namespace CFSG.Quasithin.Chapter2.LinearShadows.Single
variable {G : Type*} [Group G] [Finite G] {M : Subgroup G}

theorem source_field_core_centralizer_card_square
    (d : MinimalBlockSetup M) (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    (hST : (d.S : Subgroup d.H).map d.H.subtype < (T : Subgroup G))
    (hsingle : d.L0 = d.block) {n : ℕ} (hL : ChapterC.IsL2EvenBlock d.block n)
    (hM : IsMaximalTwoLocal M) (hTM : (T : Subgroup G) ≤ M)
    (hu : ∀ K : Subgroup G, IsMaximalTwoLocal K → (T : Subgroup G) ≤ K → K = M)
    (c : CyclicTorusSetup d T n)
    (s : G) (hs : s ∈ (d.S : Subgroup d.H).map d.H.subtype ⊓ normalizer (c.hall : Set G))
    (hs2 : orderOf s = 2) :
    Nat.card (twoCore d.H ⊓ centralizer ({s} : Set G) : Subgroup G)^2 = Nat.card (twoCore d.H) := by
  let R := Stellmacher.elementaryAbelianMaxJ ((d.S : Subgroup d.H).map d.H.subtype)
  let Q := twoCore d.H
  let N := Q.subgroupOf R
  let α := (R.normalizerMonoidHom ⟨s,source_field_actor_normalizes_thompson d s hs.1⟩).toMonoidHom
  let hN : ∀ x ∈ N, α x ∈ N := source_field_actor_preserves_core d s hs.1
  let E := (α.restrict hN).eqLocus (MonoidHom.id N)
  have hQR : Q ≤ R := le_sSup (d.core_source hG T hST).2.2
  let e : E ≃ (Q ⊓ centralizer ({s} : Set G) : Subgroup G) :=
    { toFun := fun u => ⟨((u.val : R) : G),u.val.property,by
        apply mem_centralizer_singleton_iff.mpr
        have he := congrArg (fun v : N => ((v : R) : G)) u.property
        change s * ((u.val : R) : G) * s⁻¹ = ((u.val : R) : G) at he
        exact (mul_inv_eq_iff_eq_mul.mp he).symm⟩
      invFun := fun q => ⟨⟨⟨q,hQR q.property.1⟩,q.property.1⟩,by
        apply Subtype.ext
        apply Subtype.ext
        exact mul_inv_eq_iff_eq_mul.mpr (mem_centralizer_singleton_iff.mp q.property.2).symm⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  have hc := source_field_involution_core_fixed_card d hG T hST hsingle hL hM hTM hu c s hs hs2
  change Nat.card E ^ 2 = Nat.card N at hc
  rw [Nat.card_congr e,Nat.card_congr (subgroupOfEquivOfLe hQR).toEquiv] at hc
  exact hc

theorem source_centerless_field_plane_card
    (d : MinimalBlockSetup M) (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    (hST : (d.S : Subgroup d.H).map d.H.subtype < (T : Subgroup G))
    (hsingle : d.L0 = d.block) {n : ℕ} (hL : ChapterC.IsL2EvenBlock d.block n)
    (hM : IsMaximalTwoLocal M) (hTM : (T : Subgroup G) ≤ M)
    (hu : ∀ K : Subgroup G, IsMaximalTwoLocal K → (T : Subgroup G) ≤ K → K = M)
    (c : CyclicTorusSetup d T n) (hZ : center (d.block.map d.H.subtype) = ⊥)
    (s : G) (hs : s ∈ (d.S : Subgroup d.H).map d.H.subtype ⊓ normalizer (c.hall : Set G))
    (hs2 : orderOf s = 2) :
    Nat.card (ChapterC.Section05.ConjugateSource.sourceModule (d.block.map d.H.subtype) ⊓
      centralizer ({s} : Set G) : Subgroup G) = 2^n := by
  let L := d.block.map d.H.subtype
  let Q := twoCore d.H
  have hK := hL.of_mulEquiv (equivMapOfInjective d.block d.H.subtype d.H.subtype_injective)
  have hcore : pCore 2 L = ChapterC.blockU L := source_block_core_eq_module d hG T hST hsingle
  have hfixed : Nat.card (ChapterC.blockFixed L) = 1 := by
    have hc := Nat.card_congr (subgroupOfEquivOfLe (hK.center_le_module hcore)).toEquiv
    change Nat.card (ChapterC.blockFixed L) = Nat.card (center L) at hc
    rw [hZ,card_bot] at hc
    exact hc
  have hQc : Nat.card Q = (2^n)^2 := by
    have hc := card_eq_card_quotient_mul_card_subgroup (ChapterC.blockFixed L)
    rw [show Nat.card (ChapterC.blockU L ⧸ ChapterC.blockFixed L) = 2^(n*2) from hK.module_card,
      hfixed,mul_one] at hc
    change Nat.card (twoCore d.H) = (2^n)^2
    rw [←(source_core_absorption d hG T hST hsingle hL hM hTM hu).2]
    change Nat.card ((pCore 2 L).map L.subtype) = (2^n)^2
    rw [card_map_of_injective L.subtype_injective,hcore,hc,pow_mul]
  have hc := source_field_core_centralizer_card_square d hG T hST hsingle hL hM hTM hu c s hs hs2
  change Nat.card (Q ⊓ centralizer ({s} : Set G) : Subgroup G)^2 = Nat.card Q at hc
  rw [hQc] at hc
  rw [(lemma_2_4_8_2 d hG T hST hsingle hL hM hTM hu).2]
  exact (Nat.pow_left_inj (by decide : 2 ≠ 0)).mp hc

/-- The full-center fixed row cannot fuse to the original field involution.
All TI and fixed-plane cardinality inputs come from the original source. -/
theorem source_field_involution_not_conj_to_full_center
    (d : MinimalBlockSetup M) (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    (hST : (d.S : Subgroup d.H).map d.H.subtype < (T : Subgroup G))
    (hsingle : d.L0 = d.block) {n : ℕ} (hL : ChapterC.IsL2EvenBlock d.block n)
    (hM : IsMaximalTwoLocal M) (hTM : (T : Subgroup G) ≤ M)
    (hu : ∀ K : Subgroup G, IsMaximalTwoLocal K → (T : Subgroup G) ≤ K → K = M)
    (c : CyclicTorusSetup d T n) (hZ : center (d.block.map d.H.subtype) = ⊥)
    (s : T) (hs : (s : G) ∈ (d.S : Subgroup d.H).map d.H.subtype ⊓ normalizer (c.hall : Set G))
    (hs2 : orderOf s = 2)
    (hsR : (s : G) ∉ Stellmacher.elementaryAbelianMaxJ ((d.S : Subgroup d.H).map d.H.subtype))
    (hclosed : ∀ r t : T, orderOf r = 2 →
      (r : G) ∈ Stellmacher.elementaryAbelianMaxJ ((d.S : Subgroup d.H).map d.H.subtype) →
      IsConj (r : G) (t : G) →
      (t : G) ∈ Stellmacher.elementaryAbelianMaxJ ((d.S : Subgroup d.H).map d.H.subtype))
    (hSylow : Chapter1.IsSylowIn 2 ((T : Subgroup G) ⊓ centralizer ({(s : G)} : Set G))
      (centralizer ({(s : G)} : Set G)))
    (x : G) (hxT : x ∈ T) (hxS : x ∉ (d.S : Subgroup d.H).map d.H.subtype)
    (hxs : x ∈ centralizer ({(s : G)} : Set G))
    (i : G) (hiZ : distinguishedZ d ≤ centralizer ({i} : Set G)) : ¬ IsConj i (s : G) := by
  have hplane := source_centerless_field_plane_card d hG T hST hsingle hL hM hTM hu c hZ
    (s : G) hs ((orderOf_injective (T : Subgroup G).subtype (T : Subgroup G).subtype_injective s).trans hs2)
  exact source_not_conj_of_full_center_centralized d hG T hST hsingle hL hM hTM hu hZ
    (source_distinguished_TI d hG T hST hsingle hL hM hTM hu) s hs.1 hsR hclosed hSylow
    x hxT hxS hplane.le hxs i hiZ

end CFSG.Quasithin.Chapter2.LinearShadows.Single
