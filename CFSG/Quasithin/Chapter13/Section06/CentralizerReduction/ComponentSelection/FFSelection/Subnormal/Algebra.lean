module

public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentSelection.Seeds
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.LocalSetup.ModuleMarking
public import Theory.GroupTheory.CComponent.QuotientLifting
public import Theory.GroupTheory.Commutator.CentralizingComplement
public import Theory.GroupTheory.PResidual.SubnormalCoreAction
public import Theory.GroupTheory.PResidual.PerfectCover


/-!
# Algebraic reductions for the subnormal obstruction

Subnormality kills the two-core of the literal star image. The marked A₅
seed proves that image nontrivial, so its earlier cubic quotient forces
order three. A normalizer of index at most two containing the actual Sylow
two-subgroup is the whole quotient. Its full preimage has the same moved
subgroup as L_v, and hence normalizes that subgroup in G_v.

Residual commutator idempotence places [V,L_v] inside [U_v,L_v] without
requiring V ≤ U_v. Equal orders then identify them, and adjoining the central
line ⟨v⟩ reconstructs the forbidden G_v-invariance of V_v.

The final helper still takes the two B.5.6 bounds explicitly. Their derivation
from the complete source alternatives is required before asserting 13.6.10.
The other local premises are the module data on p.926 and 13.6.8.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
Lemma 13.6.10, printed p.928.
-/

@[expose] public section
open Subgroup
namespace CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentSelection.Subnormal
variable {G : Type*} [Group G]

/-- A core-free image of a group with cubic two-core quotient has order
three as soon as it is nontrivial. -/
private theorem card_of_cubic_quotient_of_twoCore_eq_bot [Finite G] {D : Type*} [Group D] [Finite D]
    (f : G →* D) (hf : Function.Surjective f)
    (hcore : pCore 2 D = ⊥) (hcard : Nat.card (G ⧸ pCore 2 G) = 3)
    (hne : Nontrivial D) : Nat.card D = 3 := by
  have hm : (pCore 2 G).map f ≤ pCore 2 D :=
    le_sSup ⟨(inferInstance : (pCore 2 G).Normal).map f hf, pCore_isPGroup.map f⟩
  rw [hcore] at hm
  have hk : pCore 2 G ≤ f.ker := (Subgroup.map_eq_bot_iff _).mp (le_bot_iff.mp hm)
  let q := QuotientGroup.lift (pCore 2 G) f hk
  have hq : Function.Surjective q := by
    intro d
    obtain ⟨g, rfl⟩ := hf d
    exact ⟨QuotientGroup.mk' (pCore 2 G) g, rfl⟩
  have hd : Nat.card D ∣ 3 := hcard ▸ card_dvd_of_surjective q hq
  rcases (Nat.dvd_prime (by decide : Nat.Prime 3)).mp hd with he | he
  · let := hne
    obtain ⟨d, hd⟩ := exists_ne (1 : D)
    exact (hd ((Nat.card_eq_one_iff_unique.mp he).1.elim d 1)).elim
  · exact he

/-- The order-three reduction is applied to the literal star image. -/
theorem star_card_three [Finite G] (L : Subgroup G) (z v : G)
    (hcore : pCore 2 (Gstar z v) = ⊥)
    (hcard : Nat.card (Lv L v ⧸ pCore 2 (Lv L v)) = 3)
    (hs : (starImage z v (Lv L v)).IsSubnormal)
    (hne : starImage z v (Lv L v) ≠ ⊥) :
    Nat.card (starImage z v (Lv L v)) = 3 := by
  let A := Lv L v
  let B := starImage z v A
  let f : A →* B :=
    ((starMk z v).comp (inclusion (Lv_le_Gv L v))).codRestrict B
      (fun a => mem_map_of_mem _ a.property)
  have hf : Function.Surjective f := by
    rintro ⟨b, a, ha, rfl⟩
    exact ⟨⟨a, ha⟩, rfl⟩
  have hc : pCore 2 B = ⊥ := by
    rw [pCore_subnormal_eq_comap 2 hs, hcore, MonoidHom.comap_bot]
    exact B.subtype.ker_eq_bot B.subtype_injective
  have hn : Nontrivial B := (bot_or_nontrivial B).resolve_left hne
  exact card_of_cubic_quotient_of_twoCore_eq_bot f hf hc hcard hn

/-- Nontriviality comes from the actual binary A₅ action on the marked seed. -/
theorem marked_star_ne_bot [Finite G] {L V : Subgroup G} (s : A5Module.Marking L V) :
    starImage (A5Module.markedZ s) (A5Module.markedV s)
      (Lv L (A5Module.markedV s)) ≠ ⊥ := by
  intro he
  have hc := (starImage_eq_bot_iff _ _ _ (Lv_le_Gv L _)).mp he
  obtain ⟨c, hcr, hca⟩ := A5Module.exists_residual_cubic s
  have hcL : (c : G) ∈ Lv L (A5Module.markedV s) := ⟨c, hcr, rfl⟩
  have hcomm := mem_centralizer_iff.mp (hc hcL) _
    (z_mem_Uv (A5Module.markedZ s) (A5Module.markedV s))
  have hfix : MulAut.conj (c : G) (A5Module.markedZ s) = A5Module.markedZ s := by
    change (c : G) * A5Module.markedZ s * (c : G)⁻¹ = _
    rw [← hcomm, mul_inv_cancel_right]
  have heq := s.equivariant (inclusion inf_le_left c)
    BinaryPermutation.FiveCentralizerGeometry.z
  rw [hca] at heq
  have hid := s.injective (heq.symm.trans hfix)
  have hd := congrArg (fun x : Multiplicative BinaryPermutation.FiveCentralizerGeometry.Space =>
    x.toAdd.val 4) hid
  have hcalc : (BinaryPermutation.FiveCentralizerGeometry.act
      BinaryPermutation.FiveCentralizerGeometry.cubic
      BinaryPermutation.FiveCentralizerGeometry.z).val 4 = 1 := by decide +kernel
  change (BinaryPermutation.FiveCentralizerGeometry.act
    BinaryPermutation.FiveCentralizerGeometry.cubic
    BinaryPermutation.FiveCentralizerGeometry.z).val 4 = 0 at hd
  rw [hcalc] at hd
  exact (by decide : (1 : ZMod 2) ≠ 0) hd

/-- The first sentence of 13.6.10, with nontriviality discharged by the
actual A₅ marking. The cubic two-core quotient is the earlier p.926 datum. -/
theorem marked_star_card_three [Finite G] {L V : Subgroup G} (s : A5Module.Marking L V)
    (hcore : pCore 2 (Gstar (A5Module.markedZ s) (A5Module.markedV s)) = ⊥)
    (hcard : Nat.card (Lv L (A5Module.markedV s) ⧸
      pCore 2 (Lv L (A5Module.markedV s))) = 3)
    (hs : (starImage (A5Module.markedZ s) (A5Module.markedV s)
      (Lv L (A5Module.markedV s))).IsSubnormal) :
    Nat.card (starImage (A5Module.markedZ s) (A5Module.markedV s)
      (Lv L (A5Module.markedV s))) = 3 :=
  star_card_three L _ _ hcore hcard hs (marked_star_ne_bot s)

/-- A Sylow two-subgroup in the normalizer excludes an orbit of length two. -/
private theorem normal_of_sylow_normalizes_of_index_le_two [Finite G]
    (A : Subgroup G) (S : Sylow 2 G)
    (hn : (S : Subgroup G) ≤ normalizer (A : Set G))
    (hi : (normalizer (A : Set G)).index ≤ 2) : A.Normal := by
  have hp := (normalizer (A : Set G)).index_ne_zero_of_finite
  have hne : (normalizer (A : Set G)).index ≠ 2 := by
    intro he
    have hd := index_dvd_of_le hn
    rw [he] at hd
    exact S.not_dvd_index hd
  have h1 : (normalizer (A : Set G)).index = 1 := by omega
  exact normalizer_eq_top_iff.mp (index_eq_one.mp h1)

/-- The source Sylow normalization is transported through the actual quotient. -/
theorem star_sylow_normalizes [Finite G]
    (L T : Subgroup G) (z v : G) (S : Sylow 2 (Gv v))
    (hS : (S : Subgroup (Gv v)).map (Gv v).subtype = Tv T v)
    (hn : Tv T v ≤ normalizer (Lv L v : Set G)) :
    (S.mapSurjective (starMk_surjective z v) : Subgroup (Gstar z v)) ≤
      normalizer (starImage z v (Lv L v) : Set (Gstar z v)) := by
  change (S : Subgroup (Gv v)).map (starMk z v) ≤ _
  apply le_trans (map_mono (show (S : Subgroup (Gv v)) ≤
    normalizer ((Lv L v).subgroupOf (Gv v) : Set (Gv v)) from ?_))
    (le_normalizer_map _)
  rw [← subgroupOf_normalizer_eq (Lv_le_Gv L v)]
  intro s hs
  exact hn (hS ▸ mem_map_of_mem (Gv v).subtype hs)

/-- A short conjugacy orbit and the actual Sylow normalization force normality. -/
theorem star_normal_of_index_le_two [Finite G]
    (L T : Subgroup G) (z v : G) (S : Sylow 2 (Gv v))
    (hS : (S : Subgroup (Gv v)).map (Gv v).subtype = Tv T v)
    (hn : Tv T v ≤ normalizer (Lv L v : Set G))
    (hi : (normalizer (starImage z v (Lv L v) : Set (Gstar z v))).index ≤ 2) :
    (starImage z v (Lv L v)).Normal :=
  normal_of_sylow_normalizes_of_index_le_two _ (S.mapSurjective (starMk_surjective z v))
    (star_sylow_normalizes L T z v S hS hn) hi

/-- The full action preimage has the same commutator on U_v as the original actor. -/
theorem commutator_starPreimage_starImage (z v : G) (A : Subgroup G)
    (hA : A ≤ Gv v) :
    ⁅Uv z v, starPreimage z v (starImage z v A)⁆ = ⁅Uv z v, A⁆ := by
  let C := (starMk z v).ker.map (Gv v).subtype
  have hC : C ≤ centralizer (Uv z v : Set G) := by
    rintro x ⟨y, hy, rfl⟩
    rw [starMk_ker] at hy
    exact hy
  have hgen : C ⊔ A = starPreimage z v (starImage z v A) := by
    unfold starPreimage starImage
    rw [comap_map_eq, Subgroup.map_sup, map_subgroupOf_eq_of_le hA]
    exact sup_comm _ _
  exact (commutator_eq_of_centralizing_sup hgen hC
    (hA.trans (Gv_normalizes_Uv z v))).symm

/-- Normality of the quotient actor gives invariance of its actual moved subgroup. -/
theorem moved_normalized_of_star_normal (L : Subgroup G) (z v : G)
    (hn : (starImage z v (Lv L v)).Normal) :
    Gv v ≤ normalizer ((⁅Uv z v, Lv L v⁆ : Subgroup G) : Set G) := by
  let := hn
  rw [← commutator_starPreimage_starImage z v (Lv L v) (Lv_le_Gv L v)]
  intro g hg
  apply mem_normalizer_iff_map_conj_eq.mpr
  rw [map_commutator,
    mem_normalizer_iff_map_conj_eq.mp (Gv_normalizes_Uv z v hg),
    mem_normalizer_iff_map_conj_eq.mp (starPreimage_normalized z v _ hg)]

/-- Once the moved-space comparison is known, the central line reconstructs
exactly the forbidden relative normality in 13.6.8. -/
theorem Vv_normalized_of_star_normal_of_moved_eq
    (L V : Subgroup G) (z v : G)
    (hn : (starImage z v (Lv L v)).Normal)
    (he : ⁅Uv z v, Lv L v⁆ = ⁅V, Lv L v⁆)
    (hsplit : Vv L z v = zpowers v ⊔ ⁅V, Lv L v⁆) :
    Gv v ≤ normalizer (Vv L z v : Set G) := by
  rw [hsplit, ← he]
  intro g hg
  apply mem_normalizer_iff_map_conj_eq.mpr
  rw [Subgroup.map_sup, mem_normalizer_iff_map_conj_eq.mp
    (moved_normalized_of_star_normal L z v hn hg)]
  congr 1
  apply mem_normalizer_iff_map_conj_eq.mp
  apply centralizer_le_normalizer (zpowers v : Set G)
  simpa only [zpowers_eq_closure, centralizer_closure] using (show g ∈ centralizer ({v} : Set G) from hg)

/-- The literal two-residual acts idempotently on the original binary module. -/
theorem local_moved_idempotent [Finite G] (L V : Subgroup G) (v : G)
    (hV : IsPGroup 2 V) (hn : Lv L v ≤ normalizer (V : Set G)) :
    ⁅⁅V, Lv L v⁆, Lv L v⁆ = ⁅V, Lv L v⁆ :=
  commutator_isPPerfect_idempotent (Lv L v) V
    (isPPerfect_embedded_pResidual 2 (L ⊓ Gv v)) hV hn

/-- The smaller moved plane is contained in the U_v commutator even though
V need not be contained in U_v. Idempotence supplies the required inclusion. -/
theorem local_moved_le [Finite G] (L V : Subgroup G) (z v : G)
    (hV : IsPGroup 2 V) (hn : Lv L v ≤ normalizer (V : Set G))
    (hsplit : Vv L z v = zpowers v ⊔ ⁅V, Lv L v⁆) :
    ⁅V, Lv L v⁆ ≤ ⁅Uv z v, Lv L v⁆ := by
  have hsmall : ⁅V, Lv L v⁆ ≤ Uv z v :=
    (show ⁅V, Lv L v⁆ ≤ Vv L z v from hsplit ▸ le_sup_right).trans (Vv_le_Uv L z v)
  calc
    ⁅V, Lv L v⁆ = ⁅⁅V, Lv L v⁆, Lv L v⁆ := (local_moved_idempotent L V v hV hn).symm
    _ ≤ ⁅Uv z v, Lv L v⁆ := commutator_mono hsmall le_rfl

/-- The B.5.6 order bound, once proved, identifies the two actual moved subgroups. -/
theorem moved_eq_of_card_le_four [Finite G] (L V : Subgroup G) (z v : G)
    (hV : IsPGroup 2 V) (hn : Lv L v ≤ normalizer (V : Set G))
    (hsplit : Vv L z v = zpowers v ⊔ ⁅V, Lv L v⁆)
    (hsmall : Nat.card ↥(⁅V, Lv L v⁆ : Subgroup G) = 4)
    (hlarge : Nat.card ↥(⁅Uv z v, Lv L v⁆ : Subgroup G) ≤ 4) :
    ⁅Uv z v, Lv L v⁆ = ⁅V, Lv L v⁆ :=
  (eq_of_le_of_card_ge (local_moved_le L V z v hV hn hsplit)
    (hsmall ▸ hlarge)).symm

/-- The final elementary argument in 13.6.10. The two B.5.6 bounds are
explicit premises of this helper, and remain to be derived for source assembly.
The local module data are the paragraph preceding 13.6.4; the last premise
is precisely the nonnormality clause of 13.6.8. -/
theorem contradiction_of_classification_bounds [Finite G]
    (L V T : Subgroup G) (z v : G) (S : Sylow 2 (Gv v))
    (hS : (S : Subgroup (Gv v)).map (Gv v).subtype = Tv T v)
    (hT : Tv T v ≤ normalizer (Lv L v : Set G))
    (hV : IsPGroup 2 V) (hL : Lv L v ≤ normalizer (V : Set G))
    (hsplit : Vv L z v = zpowers v ⊔ ⁅V, Lv L v⁆)
    (hsmall : Nat.card ↥(⁅V, Lv L v⁆ : Subgroup G) = 4)
    (hlarge : Nat.card ↥(⁅Uv z v, Lv L v⁆ : Subgroup G) ≤ 4)
    (horbit : (normalizer (starImage z v (Lv L v) : Set (Gstar z v))).index ≤ 2)
    (hnormal : ¬ ((Vv L z v).subgroupOf (Gv v)).Normal) : False := by
  have hn := star_normal_of_index_le_two L T z v S hS hT horbit
  have he := moved_eq_of_card_le_four L V z v hV hL hsplit hsmall hlarge
  exact hnormal (normal_subgroupOf_of_le_normalizer
    (Vv_normalized_of_star_normal_of_moved_eq L V z v hn he hsplit))

end CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentSelection.Subnormal

end
