module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericExceptionalCartanGlobalPrimeConstruction
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericExceptionalLinearFieldEscape
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericExceptionalLinearFieldEscapeModulesGeometry
public import CFSG.Quasithin.ChapterG.Section02.Binary.FourAction
public import Theory.GroupTheory.ConjugateSpanCentralizer
/-!
# Natural coordinates for the original cubic plane

The cyclic Cartan quotient makes (T ∩ L)C invariant under T. Counting
this product proves [⟨C,T⟩:T] = 3. In the nonabelian-span branch the
Sylow action on the four-group is nontrivial, and transitivity of L₂
makes the full action S₃. The given Sylow centralizer then identifies
its kernel with O₂(L₂T). Passing the two-residual through this actual
action constructs the natural C₃ coordinates required by G.2.3.

No quotient model, natural-module witness or nontrivial star image is
assumed. The companion application uses these coordinates on the
literal centralizer span. This is the G.2.3 input step of 5.1.23;
the strict cubic bound and constituent obstruction remain to be proved.
Source: Aschbacher--Smith, printed pp.333--334,645, refs/quasithin.pdf.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open CFSG.Quasithin
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric.CubicEscape
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L H A B C : Subgroup G} {n : ℕ}
/-- The cubic and the original Sylow subgroup have the source index three. -/
theorem cartan_cubic_join_card
    (c : LinearFieldCartan T L H A B C n)
    (hTL : (T : Subgroup G) ≤ normalizer (L : Set G))
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2 ^ n)) :
    Nat.card (actor T C ⊔ (T : Subgroup G) : Subgroup G) = 3 * Nat.card T := by
  let U := (T : Subgroup G) ⊓ L
  have hTU : (T : Subgroup G) ≤ normalizer (U : Set G) :=
    (le_inf (T : Subgroup G).le_normalizer hTL).trans inf_normalizer_le_normalizer_inf
  have hTN : (T : Subgroup G) ≤ normalizer (localBorel T L : Set G) :=
    (le_inf hTL (hTU.trans (normalizer (U : Set G)).le_normalizer)).trans
      inf_normalizer_le_normalizer_inf
  have hnorm := hTN.trans
    (Prime.cartan_subgroup_preimage_normalized c.toCartanPair hTL hpsl c.cubic_le)
  have hCL : C ≤ L := c.cubic_le.trans (c.left_le.trans inf_le_left)
  have hCU : C ≤ normalizer (U : Set G) := c.cubic_le.trans (c.left_le.trans inf_le_right)
  have hinter : (U ⊔ C) ⊓ (T : Subgroup G) = U := by
    apply le_antisymm
    · exact le_inf inf_le_right (inf_le_left.trans (sup_le inf_le_right hCL))
    · exact le_inf le_sup_left inf_le_left
  have he : (U ⊔ C) ⊔ (T : Subgroup G) = C ⊔ (T : Subgroup G) := by
    exact le_antisymm
      (sup_le (sup_le (inf_le_left.trans le_sup_right) le_sup_left) le_sup_right)
      (sup_le (le_sup_right.trans le_sup_left) le_sup_right)
  obtain ⟨k, hk⟩ := (T.isPGroup'.to_le (show U ≤ (T : Subgroup G) from inf_le_left)).exists_card_eq
  have hd : Disjoint U C := disjoint_of_coprime_natCard (by
    rw [hk, c.cubic_card]
    exact (by decide : Nat.Coprime 2 3).pow_left k)
  have hm := card_mul_eq_card_inf_mul_card_sup_of_normalizes (U ⊔ C) (T : Subgroup G) hnorm
  rw [card_sup_eq_mul_of_normalizes_of_disjoint U C hCU hd, hinter, he, mul_assoc] at hm
  have hj : actor T C ⊔ (T : Subgroup G) = C ⊔ (T : Subgroup G) := by
    apply le_antisymm
    · exact sup_le (conjugateSpanBy_le le_sup_left
        (le_sup_right.trans (C ⊔ (T : Subgroup G)).le_normalizer)) le_sup_right
    · exact sup_le ((le_conjugateSpanBy _ _).trans le_sup_left) le_sup_right
  rw [hj]
  exact (Nat.eq_of_mul_eq_mul_left (Nat.card_pos (α := U)) hm).symm.trans
    (by rw [c.cubic_card])

variable {z : G}

/-- Relative reducedness supplies normalization of the actual plane. -/
theorem LocalData.plane_normalized (d : LocalData T H C z) :
    actor T C ⊔ (T : Subgroup G) ≤ normalizer (plane C z : Set G) :=
  (normal_subgroupOf_iff_le_normalizer d.plane_le).mp d.reduced.normal

/-- Transitivity identifies the plane with the L₂-orbit span of the point. -/
theorem LocalData.plane_span (d : LocalData T H C z) :
    plane C z = conjugateSpanBy (zpowers z) (actor T C) := by
  apply le_antisymm ?_ (conjugateSpanBy_le d.g2.point_le
    (le_sup_left.trans d.plane_normalized))
  intro v hv
  by_cases hv1 : v = 1
  · exact hv1.symm ▸ (conjugateSpanBy (zpowers z) (actor T C)).one_mem
  obtain ⟨l, hl, he⟩ := d.transitive v hv hv1
  exact subset_closure ⟨l, hl, z, mem_zpowers z, he⟩

omit [Finite G] in
private theorem action_ker {P V : Subgroup G} (hn : P ≤ normalizer (V : Set G)) :
    (V.normalizerMonoidHom.comp (inclusion hn)).ker = (centralizer (V : Set G)).subgroupOf P := by
  rw [← MonoidHom.comap_ker, normalizerMonoidHom_ker]
  rfl

private theorem action_on_sylow (d : LocalData T H C z)
    (s : (setup T (centralizer ({z} : Set G)) C z).Hypothesis)
    (hne : ¬ IsMulCommutative (conjugateSpanBy (plane C z) (centralizer ({z} : Set G)))) :
    Nat.card ((plane C z).normalizerMonoidHom.comp (inclusion d.g2.T_normalizes_V)).range = 2 := by
  let V := plane C z
  let : IsElementaryAbelian 2 V := d.g2.elementary
  let : Nontrivial V := Finite.one_lt_card_iff_nontrivial.mp (by rw [d.plane_card]; decide)
  let : IsKleinFour V := ⟨d.plane_card, IsElementaryAbelian.exponent_eq_prime⟩
  let hTN : (T : Subgroup G) ≤ normalizer (V : Set G) := d.g2.T_normalizes_V
  let t : T →* MulAut V := V.normalizerMonoidHom.comp (inclusion hTN)
  have hd : Nat.card t.range ∣ 6 := by simpa only [IsKleinFour.card_mulAut] using t.range.card_subgroup_dvd_card
  obtain ⟨k, hk⟩ := (T.isPGroup'.of_surjective t.rangeRestrict t.rangeRestrict_surjective).exists_card_eq
  have hkle : k ≤ 1 := by
    by_contra hh
    have : 4 ∣ 6 := (pow_dvd_pow 2 (by omega : 2 ≤ k)).trans (hk ▸ hd)
    norm_num at this
  have hkpos : k ≠ 0 := by
    intro he
    have hr : t.range = ⊥ := card_eq_one.mp (by simpa only [he, pow_zero] using hk)
    have hTC : (T : Subgroup G) ≤ centralizer (V : Set G) := by
      intro x hx
      have hxk : (⟨x,hx⟩ : T) ∈ t.ker := by
        have hh : t ⟨x,hx⟩ ∈ t.range := ⟨⟨x,hx⟩, rfl⟩
        rw [hr] at hh
        exact hh
      change (⟨x,hx⟩ : T) ∈ (centralizer (V : Set G)).subgroupOf (T : Subgroup G)
      rw [← action_ker hTN]
      exact hxk
    exact hne ((conjugateSpanBy_commutative_iff V (centralizer ({z} : Set G))).mpr
      (le_centralizer_iff.mp (s.U_normal_in_T.1.trans hTC)))
  change Nat.card t.range = 2
  rw [hk, show k = 1 by omega]
  rfl


private theorem full_action (d : LocalData T H C z)
    (s : (setup T (centralizer ({z} : Set G)) C z).Hypothesis)
    (hne : ¬ IsMulCommutative (conjugateSpanBy (plane C z) (centralizer ({z} : Set G)))) :
    Function.Surjective ((plane C z).normalizerMonoidHom.comp (inclusion d.plane_normalized)) := by
  classical
  let V := plane C z
  let J := actor T C ⊔ (T : Subgroup G)
  let : IsElementaryAbelian 2 V := d.g2.elementary
  let : Nontrivial V := Finite.one_lt_card_iff_nontrivial.mp (by rw [d.plane_card]; decide)
  let : IsKleinFour V := ⟨d.plane_card, IsElementaryAbelian.exponent_eq_prime⟩
  let f : J →* MulAut V := V.normalizerMonoidHom.comp (inclusion d.plane_normalized)
  let hTN : (T : Subgroup G) ≤ normalizer (V : Set G) := d.g2.T_normalizes_V
  let t : T →* MulAut V := V.normalizerMonoidHom.comp (inclusion hTN)
  have ht : Nat.card t.range = 2 := action_on_sylow d s hne
  have htf : t.range ≤ f.range := by
    rintro y ⟨x, rfl⟩
    exact ⟨⟨x, mem_sup_right x.property⟩, rfl⟩
  have htwo : 2 ∣ Nat.card f.range := by
    rw [← ht]
    exact card_dvd_of_le htf
  let zv : V := ⟨z, d.g2.point_le (mem_zpowers z)⟩
  have hzv : zv ≠ 1 := fun he => d.point_ne (congrArg Subtype.val he)
  let eval : f.range → {v : V // v ≠ 1} := fun a =>
    ⟨a.val zv, fun he => hzv (a.val.injective (he.trans a.val.map_one.symm))⟩
  have hev : Function.Surjective eval := by
    rintro ⟨v, hv⟩
    obtain ⟨l, hl, he⟩ := d.transitive v v.property (fun hh => hv (Subtype.ext hh))
    refine ⟨⟨f ⟨l, mem_sup_left hl⟩, ⟨⟨l, mem_sup_left hl⟩, rfl⟩⟩, ?_⟩
    apply Subtype.ext
    apply Subtype.ext
    exact he
  have hthree : 3 ≤ Nat.card f.range := by
    have hc : Nat.card {v : V // v ≠ 1} = 3 := by
      let : Fintype V := Fintype.ofFinite V
      rw [Nat.card_eq_fintype_card, Fintype.card_subtype_compl]
      simp
    exact hc ▸ Nat.card_le_card_of_surjective eval hev
  have hd : Nat.card f.range ∣ 6 :=
    by simpa only [IsKleinFour.card_mulAut] using f.range.card_subgroup_dvd_card
  have hle := Nat.le_of_dvd (by decide : 0 < 6) hd
  have heq : Nat.card f.range = 6 := by
    revert hd htwo
    interval_cases hh : Nat.card f.range <;> norm_num
  apply MonoidHom.range_eq_top.mp
  exact eq_top_of_card_eq _ (heq.trans (IsKleinFour.card_mulAut V).symm)


private theorem full_action_kernel (c : LinearFieldCartan T L H A B C n)
    (hTL : (T : Subgroup G) ≤ normalizer (L : Set G))
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2 ^ n))
    (d : LocalData T H C z)
    (s : (setup T (centralizer ({z} : Set G)) C z).Hypothesis)
    (hne : ¬ IsMulCommutative (conjugateSpanBy (plane C z) (centralizer ({z} : Set G)))) :
    ((plane C z).normalizerMonoidHom.comp (inclusion d.plane_normalized)).ker =
      pCore 2 (actor T C ⊔ (T : Subgroup G) : Subgroup G) := by
  let V := plane C z
  let J := actor T C ⊔ (T : Subgroup G)
  let f : J →* MulAut V := V.normalizerMonoidHom.comp (inclusion d.plane_normalized)
  let hTN : (T : Subgroup G) ≤ normalizer (V : Set G) := d.g2.T_normalizes_V
  let t : T →* MulAut V := V.normalizerMonoidHom.comp (inclusion hTN)
  let : IsElementaryAbelian 2 V := d.g2.elementary
  let : Nontrivial V := Finite.one_lt_card_iff_nontrivial.mp (by rw [d.plane_card]; decide)
  let : IsKleinFour V := ⟨d.plane_card, IsElementaryAbelian.exponent_eq_prime⟩
  have htk : t.ker.map (T : Subgroup G).subtype = J.pCoreIn 2 := by
    change (V.normalizerMonoidHom.comp (inclusion hTN)).ker.map (T : Subgroup G).subtype = J.pCoreIn 2
    rw [action_ker, subgroupOf_map_subtype, inf_comm]
    exact d.centralizer_eq
  have htkc : Nat.card t.ker = Nat.card (pCore 2 J) := by
    calc
      Nat.card t.ker = Nat.card (t.ker.map (T : Subgroup G).subtype) :=
        (card_map_of_injective (K := t.ker) (f := (T : Subgroup G).subtype)
          (T : Subgroup G).subtype_injective).symm
      _ = Nat.card (pCore 2 J) := by rw [htk, pCoreIn, card_map_of_injective J.subtype_injective]
  have htcard := t.ker.card_mul_index
  rw [index_ker, show Nat.card t.range = 2 from action_on_sylow d s hne, htkc] at htcard
  have hfcard := f.ker.card_mul_index
  have hr : Nat.card f.range = 6 := by
    rw [(MonoidHom.range_eq_top.mpr (full_action d s hne)), Nat.card_congr topEquiv.toEquiv]
    exact IsKleinFour.card_mulAut V
  rw [index_ker, hr] at hfcard
  have hjcard : Nat.card J = 3 * Nat.card T := cartan_cubic_join_card c hTL hpsl
  have hle : pCore 2 J ≤ f.ker := by
    rw [action_ker]
    intro x hx
    exact (d.centralizer_eq.ge (mem_map_of_mem J.subtype hx)).2
  have hfc : Nat.card f.ker = Nat.card (pCore 2 J) := by omega
  exact (eq_of_le_of_card_ge hle hfc.le).symm

/-- Construct the genuine G.2.3 binary natural data on the original subgroups. -/
def LocalData.binaryNaturalData
    (c : LinearFieldCartan T L H A B C n)
    (hTL : (T : Subgroup G) ≤ normalizer (L : Set G))
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2 ^ n))
    (d : LocalData T H C z)
    (s : (setup T (centralizer ({z} : Set G)) C z).Hypothesis)
    (hne : ¬ IsMulCommutative (conjugateSpanBy (plane C z) (centralizer ({z} : Set G)))) :
    (setup T (centralizer ({z} : Set G)) C z).BinaryNaturalData := by
  let D := setup T (centralizer ({z} : Set G)) C z
  have hLN : D.L ≤ normalizer (D.V : Set G) := le_sup_left.trans d.plane_normalized
  have hfull := full_action d s hne
  have hker := full_action_kernel c hTL hpsl d s hne
  have hres : (D.V.normalizerMonoidHom.comp (inclusion hLN)).range =
      pResidual 2 (MulAut D.V) := by
    let f := D.V.normalizerMonoidHom.comp (inclusion (sup_le hLN s.T_normalizes_V))
    have he : (pResidual 2 D.LT).map D.LT.subtype = D.L :=
      embedded_pResidual_join_pGroup D.L D.T
        ((pResidual_eq_top_iff 2 D.L).mp s.residual) T.isPGroup' s.T_normalizes_L
    have hr : pResidual 2 D.LT = D.L.subgroupOf D.LT := by
      apply map_injective D.LT.subtype_injective
      rw [he, map_subgroupOf_eq_of_le (show D.L ≤ D.LT from le_sup_left)]
    have hf : (D.L.subgroupOf D.LT).map f =
        (D.V.normalizerMonoidHom.comp (inclusion hLN)).range := by
      ext y
      constructor
      · rintro ⟨x, hx, rfl⟩
        exact ⟨⟨x, hx⟩, rfl⟩
      · rintro ⟨x, rfl⟩
        exact ⟨⟨x, mem_sup_left x.property⟩, x.property, rfl⟩
    rw [← hf, ← hr]
    exact map_pResidual_of_surjective 2 f hfull
  have hnstar : D.star D.U ≠ ⊥ := by
    intro hb
    have hUL : D.U ≤ D.LT := s.U_normal_in_T.1.trans le_sup_right
    have hk : D.U.subgroupOf D.LT ≤ pCore 2 D.LT := by
      have hm := (Subgroup.map_eq_bot_iff _).mp hb
      simpa only [QuotientGroup.ker_mk'] using hm
    have hUC : D.U ≤ centralizer (D.V : Set G) := by
      intro u hu
      have huQ := mem_map_of_mem D.LT.subtype (hk (show
        (⟨u, hUL hu⟩ : D.LT) ∈ D.U.subgroupOf D.LT from hu))
      exact (d.centralizer_eq.ge huQ).2
    exact hne ((conjugateSpanBy_commutative_iff D.V D.H).mpr (le_centralizer_iff.mp hUC))
  exact ChapterG.Section02.Setup.binaryNaturalData_of_four_action s hLN d.plane_card
    d.plane_span hfull hker hres d.point_card hnstar

end CFSG.Quasithin.Chapter6.Source.RankOneGeneric.CubicEscape
