module
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.SmallOffender.NaturalCorank.Terminal.Alignment

/-!
# A swapping element in the literal natural offender

The opposite normalizer plane lies in the conjugate maximal local subgroup.
If the full offender preserves the first moved factor, the plane fixes that
index-two offender pointwise. Its nontrivial action on the first conjugate
factor forces the entire second conjugate factor into the offender.
Point control and the TI normalizer calculations exclude this containment.
Thus an actual offender element exchanges the original two moved factors;
its commutator with the plane supplies a common nonzero diagonal.

This completes the factor-exchange step without recognizing a dihedral
quotient. Complete applies it to the terminal witness and original survivor
consumer. Source: Aschbacher--Smith, 10.2.12, printed p.755.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Matrix
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter10.SmallOffender.NaturalCorank
open Chapter3.Section02 ChapterE ChapterI.Section06To08
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  {D : FundamentalSetup KnownSimple.IsKnownSimple T L} {g : G}


omit [Finite G] in
private theorem map_conj_mul (H : Subgroup G) (a b : G) :
    H.map (MulAut.conj (a*b)).toMonoidHom =
      (H.map (MulAut.conj b).toMonoidHom).map (MulAut.conj a).toMonoidHom :=
  Subgroup.conjBy_mul H a b

omit [Finite G] in
private theorem map_conj_commutator (H K : Subgroup G) (a : G) :
    (⁅H,K⁆).map (MulAut.conj a).toMonoidHom =
      ⁅H.map (MulAut.conj a).toMonoidHom,K.map (MulAut.conj a).toMonoidHom⁆ :=
  map_commutator H K (MulAut.conj a).toMonoidHom

omit [Finite G] in
private theorem conjugate_eq_of_mem_normalizer (H : Subgroup G) {a : G}
    (ha : a ∈ normalizer (H : Set G)) :
    H.map (MulAut.conj a).toMonoidHom = H :=
  mem_normalizer_iff_map_conj_eq.mp ha

theorem natural_active_axis_le_conjugate_maximal
    (c : Configuration T D g) (m : SourceLinearThreeGeometry T D)
    (hsmall : subgroupCorank (D.fullModule.map (MulAut.conj g).toMonoidHom)
      (D.fullModule.map (MulAut.conj g).toMonoidHom ⊓ D.maximalLocal) ≤ 1)
    (hz : D.fullModule ⊓ centralizer (localOrbit T L : Set G) = ⊥)
    (hti : IsTISubgroup ⁅D.fullModule,L⁆)
    (hactive : ¬ (⁅D.fullModule,L⁆).map (MulAut.conj g).toMonoidHom ≤
      centralizer ((⁅D.fullModule,L⁆ : Subgroup G) : Set G)) :
    ⁅D.fullModule,L⁆ ⊓ normalizer
      (((⁅D.fullModule,L⁆).map (MulAut.conj g).toMonoidHom : Subgroup G) : Set G) ≤
      D.maximalLocal.map (MulAut.conj g).toMonoidHom := by
  obtain ⟨_,_,hA,_⟩ := natural_active_pair_normalizers c m hsmall hz hti hactive
  have hne : (⁅D.fullModule,L⁆).map (MulAut.conj g).toMonoidHom ⊓ D.maximalLocal ≠ ⊥ := by
    intro he
    rw [he,card_bot] at hA
    omega
  obtain ⟨b,hb1⟩ := ne_bot_iff_exists_ne_one.mp hne
  have hbne : (b : G) ≠ 1 := fun hh => hb1 (Subtype.ext hh)
  obtain ⟨w,hw,he⟩ := b.property.1
  have hw1 : w ≠ 1 := by intro hh; apply hbne; rw [←he,hh,map_one]
  have hc : centralizer ({(b : G)} : Set G) ≤
      D.maximalLocal.map (MulAut.conj g).toMonoidHom := by
    rw [←he]
    change centralizer ({(MulAut.conj g) w} : Set G) ≤ _
    rw [←CentralizerSmallKernelTransport.map_centralizer (MulAut.conj g) w]
    exact map_mono (c.pointCentralizers w hw hw1)
  intro u hu
  rw [(natural_active_pair_axis c m hsmall hz hti hactive).1] at hu
  exact hc (mem_centralizer_singleton_iff.mpr (hu.2 b b.property).symm)

theorem terminalWitness_of_active_pair_swapping_offender
    (c : Configuration T D g) (m : SourceLinearThreeGeometry T D)
    (hsmall : subgroupCorank (D.fullModule.map (MulAut.conj g).toMonoidHom)
      (D.fullModule.map (MulAut.conj g).toMonoidHom ⊓ D.maximalLocal) ≤ 1)
    (hz : D.fullModule ⊓ centralizer (localOrbit T L : Set G) = ⊥)
    (hti : IsTISubgroup ⁅D.fullModule,L⁆)
    {t : G} (ht : t ∈ (T : Subgroup G)) (htn : t ∉ normalizer (L : Set G))
    (hactive : ¬ (⁅D.fullModule,L⁆).map (MulAut.conj g).toMonoidHom ≤
      centralizer ((⁅D.fullModule,L⁆ : Subgroup G) : Set G))
    {d : G} (hd : d ∈ D.fullModule.map (MulAut.conj g).toMonoidHom)
    (hswap : (⁅D.fullModule,L⁆).map (MulAut.conj d).toMonoidHom =
      (⁅D.fullModule,L⁆).map (MulAut.conj t).toMonoidHom) :
    Nonempty (TerminalWitness T D g) := by
  obtain ⟨_,_,_,hU⟩ := natural_active_pair_normalizers c m hsmall hz hti hactive
  have hne : ⁅D.fullModule,L⁆ ⊓ normalizer
      (((⁅D.fullModule,L⁆).map (MulAut.conj g).toMonoidHom : Subgroup G) : Set G) ≠ ⊥ := by
    intro he
    rw [he,card_bot] at hU
    omega
  obtain ⟨u,hu1⟩ := ne_bot_iff_exists_ne_one.mp hne
  have hune : (u : G) ≠ 1 := fun hh => hu1 (Subtype.ext hh)
  have huN : (u : G) ∈ normalizer
      ((D.fullModule.map (MulAut.conj g).toMonoidHom : Subgroup G) : Set G) := by
    rw [←map_equiv_normalizer_eq,source_fullModule_normalizer D]
    exact natural_active_axis_le_conjugate_maximal c m hsmall hz hti hactive u.property
  apply terminalWitness_of_active_pair_common_diagonal c m hsmall hz hti ht htn hactive
    ((⁅D.fullModule,L⁆).inv_mem u.property.1)
    (hswap ▸ mem_map_of_mem (MulAut.conj d).toMonoidHom u.property.1)
    (inv_ne_one.mpr hune)
    (fun he => hune ((MulAut.conj d).injective (he.trans (map_one _).symm)))
  change (u : G)⁻¹ * (d*(u : G)*d⁻¹) ∈ _
  have hh := (mem_normalizer_iff.mp ((normalizer
    ((D.fullModule.map (MulAut.conj g).toMonoidHom : Subgroup G) : Set G)).inv_mem huN) d).mp hd
  have hprod := (D.fullModule.map (MulAut.conj g).toMonoidHom).mul_mem hh
    ((D.fullModule.map (MulAut.conj g).toMonoidHom).inv_mem hd)
  simpa only [inv_inv,mul_assoc] using hprod

theorem false_of_active_pair_swapping_offender
    (c : Configuration T D g) (m : SourceLinearThreeGeometry T D)
    (hsmall : subgroupCorank (D.fullModule.map (MulAut.conj g).toMonoidHom)
      (D.fullModule.map (MulAut.conj g).toMonoidHom ⊓ D.maximalLocal) ≤ 1)
    (hz : D.fullModule ⊓ centralizer (localOrbit T L : Set G) = ⊥)
    (hti : IsTISubgroup ⁅D.fullModule,L⁆) (hcore : DiagonalCoreAt T)
    {t : G} (ht : t ∈ (T : Subgroup G)) (htn : t ∉ normalizer (L : Set G))
    (hactive : ¬ (⁅D.fullModule,L⁆).map (MulAut.conj g).toMonoidHom ≤
      centralizer ((⁅D.fullModule,L⁆ : Subgroup G) : Set G))
    {d : G} (hd : d ∈ D.fullModule.map (MulAut.conj g).toMonoidHom)
    (hswap : (⁅D.fullModule,L⁆).map (MulAut.conj d).toMonoidHom =
      (⁅D.fullModule,L⁆).map (MulAut.conj t).toMonoidHom) : False := by
  obtain ⟨w⟩ := terminalWitness_of_active_pair_swapping_offender
    c m hsmall hz hti ht htn hactive hd hswap
  exact w.false_of_diagonal_core c m hcore hz hti

/-- An active pair forces trivial intersection with the entire opposite full module. -/
theorem natural_active_moved_inf_full_conjugate_eq_bot
    (c : Configuration T D g) (m : SourceLinearThreeGeometry T D)
    (hsmall : subgroupCorank (D.fullModule.map (MulAut.conj g).toMonoidHom)
      (D.fullModule.map (MulAut.conj g).toMonoidHom ⊓ D.maximalLocal) ≤ 1)
    (hz : D.fullModule ⊓ centralizer (localOrbit T L : Set G) = ⊥)
    (hti : IsTISubgroup ⁅D.fullModule,L⁆)
    (hactive : ¬ (⁅D.fullModule,L⁆).map (MulAut.conj g).toMonoidHom ≤
      centralizer ((⁅D.fullModule,L⁆ : Subgroup G) : Set G)) :
    ⁅D.fullModule,L⁆ ⊓ D.fullModule.map (MulAut.conj g).toMonoidHom = ⊥ := by
  let : IsElementaryAbelian 2 D.fullModule := m.full_eq_local.symm ▸ D.module_elementary
  let : IsElementaryAbelian 2 (D.fullModule.map (MulAut.conj g).toMonoidHom) :=
    IsElementaryAbelian.map _
  apply eq_bot_iff.mpr
  intro w hw
  by_contra hn
  have hw1 : w ≠ 1 := fun he => hn (mem_bot.mpr he)
  have hVM : D.fullModule.map (MulAut.conj g).toMonoidHom ≤ D.maximalLocal := by
    intro a ha
    apply c.pointCentralizers w hw.1 hw1
    exact mem_centralizer_singleton_iff.mpr (setLike_mul_comm ha hw.2)
  have hWV : ⁅D.fullModule,L⁆ ≤ D.fullModule := le_normalizer_iff_commutator_le_left.mp
    (((le_componentOrbit L T).trans (localOrbit T L).le_normalizer).trans
      D.maximalLocal_normalizes_fullModule)
  have hPM := (map_mono (f := (MulAut.conj g).toMonoidHom) hWV).trans hVM
  have hcard := (natural_active_pair_normalizers c m hsmall hz hti hactive).2.2.1
  rw [inf_of_le_left hPM,card_map_of_injective (MulAut.conj g).injective,
    natural_moved_card_of_full_fixed_eq_bot m c.nonnormal hz] at hcard
  omega

/-- If the whole offender preserves the first factor, it fixes the opposite normalizer plane. -/
theorem natural_active_offender_centralizes_axis_of_normalizes
    (c : Configuration T D g) (m : SourceLinearThreeGeometry T D)
    (hsmall : subgroupCorank (D.fullModule.map (MulAut.conj g).toMonoidHom)
      (D.fullModule.map (MulAut.conj g).toMonoidHom ⊓ D.maximalLocal) ≤ 1)
    (hz : D.fullModule ⊓ centralizer (localOrbit T L : Set G) = ⊥)
    (hti : IsTISubgroup ⁅D.fullModule,L⁆)
    (hactive : ¬ (⁅D.fullModule,L⁆).map (MulAut.conj g).toMonoidHom ≤
      centralizer ((⁅D.fullModule,L⁆ : Subgroup G) : Set G))
    (hAN : D.fullModule.map (MulAut.conj g).toMonoidHom ⊓ D.maximalLocal ≤
      normalizer ((⁅D.fullModule,L⁆ : Subgroup G) : Set G)) :
    D.fullModule.map (MulAut.conj g).toMonoidHom ⊓ D.maximalLocal ≤ centralizer
      ((⁅D.fullModule,L⁆ ⊓ normalizer
        (((⁅D.fullModule,L⁆).map (MulAut.conj g).toMonoidHom : Subgroup G) : Set G) : Subgroup G) : Set G) := by
  let W := ⁅D.fullModule,L⁆
  let V := D.fullModule.map (MulAut.conj g).toMonoidHom
  let A := V ⊓ D.maximalLocal
  let U := W ⊓ normalizer ((W.map (MulAut.conj g).toMonoidHom : Subgroup G) : Set G)
  have hUN : U ≤ normalizer (V : Set G) := by
    rw [←map_equiv_normalizer_eq,source_fullModule_normalizer D]
    exact natural_active_axis_le_conjugate_maximal c m hsmall hz hti hactive
  have hcomm : ⁅A,U⁆ ≤ W ⊓ V := le_inf
    ((commutator_mono le_rfl (show U ≤ W from inf_le_left)).trans
      (le_normalizer_iff_commutator_le_right.mp hAN))
    ((commutator_mono (show A ≤ V from inf_le_left) le_rfl).trans
      (le_normalizer_iff_commutator_le_left.mp hUN))
  exact commutator_eq_bot_iff_le_centralizer.mp (bot_unique
    (hcomm.trans_eq (natural_active_moved_inf_full_conjugate_eq_bot c m hsmall hz hti hactive)))


omit [Finite G] in
private theorem fixed_hyperplane_partner
    (V H P Q : Subgroup G) (e : G ≃* G)
    (hPV : P ≤ V) (hQV : Q ≤ V) (hi : H.relIndex V = 2)
    (hd : Disjoint P Q) (hP : P.map e.toMonoidHom ≤ P)
    (hQ : Q.map e.toMonoidHom ≤ Q)
    (hfix : ∀ a ∈ H, e a = a)
    (hmoving : ∃ p ∈ P, e p ≠ p) : Q ≤ H := by
  obtain ⟨p,hp,hpm⟩ := hmoving
  have hpH : p ∉ H := fun hh => hpm (hfix p hh)
  intro q hq
  by_contra hqH
  have hpq : p*q ∈ H := ((H.subgroupOf V).mul_mem_iff_of_index_two hi
    (a := (⟨p,hPV hp⟩ : V)) (b := ⟨q,hQV hq⟩)).mpr (iff_of_false hpH hqH)
  have he : e p * e q = p*q := by rw [←map_mul,hfix _ hpq]
  have hh : ((⟨e p,hP (mem_map_of_mem _ hp)⟩ : P),
      (⟨e q,hQ (mem_map_of_mem _ hq)⟩ : Q)) = (⟨p,hp⟩,⟨q,hq⟩) :=
    mul_injective_of_disjoint hd he
  exact hpm (congrArg (fun x : P × Q => (x.1 : G)) hh)

theorem natural_partner_normalized
    (m : SourceLinearThreeGeometry T D)
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    (hz : D.fullModule ⊓ centralizer (localOrbit T L : Set G) = ⊥)
    {t : G} (ht : t ∈ (T : Subgroup G)) (htn : t ∉ normalizer (L : Set G)) :
    D.maximalLocal ⊓ normalizer ((⁅D.fullModule,L⁆ : Subgroup G) : Set G) ≤
      normalizer (((⁅D.fullModule,L⁆).map (MulAut.conj t).toMonoidHom : Subgroup G) : Set G) := by
  let W := ⁅D.fullModule,L⁆
  let B := W.map (MulAut.conj t).toMonoidHom
  let V := D.fullModule
  let : IsElementaryAbelian 2 V := by
    change IsElementaryAbelian 2 D.fullModule
    rw [m.full_eq_local]
    exact D.module_elementary
  have hgen : V = W ⊔ B := source_nonnormal_fullModule_eq_moved_pair D hn ht (m.crossed t ht htn)
  have hWV : W ≤ V := le_sup_left.trans_eq hgen.symm
  have hBV : B ≤ V := le_sup_right.trans_eq hgen.symm
  have hBW : B ≤ normalizer (W : Set G) :=
    ((hBV.trans V.le_centralizer).trans (centralizer_le hWV)).trans (Subgroup.centralizer_le_normalizer _)
  have hf : V ⊓ centralizer (L : Set G) = B := by
    rw [hgen,sup_comm,inf_centralizer_sup_of_centralizing B W L hBW (m.crossed t ht htn),
      moved_fixed_eq_bot_of_full_fixed_eq_bot m hn hz,sup_bot_eq]
  change D.maximalLocal ⊓ normalizer (W : Set G) ≤ normalizer (B : Set G)
  rw [←hf]
  exact (le_inf (inf_le_left.trans D.maximalLocal_normalizes_fullModule)
    ((source_original_moved_stabilizer_le_component_normalizer D ht htn
      (m.crossed t ht htn)).trans (normalizer_le_normalizer_centralizer _))).trans
      inf_normalizer_le_normalizer_inf

theorem natural_conjugate_partner_normalized
    (m : SourceLinearThreeGeometry T D)
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    (hz : D.fullModule ⊓ centralizer (localOrbit T L : Set G) = ⊥)
    {t : G} (ht : t ∈ (T : Subgroup G)) (htn : t ∉ normalizer (L : Set G)) :
    D.maximalLocal.map (MulAut.conj g).toMonoidHom ⊓
      normalizer (((⁅D.fullModule,L⁆).map (MulAut.conj g).toMonoidHom : Subgroup G) : Set G) ≤
      normalizer (((⁅D.fullModule,L⁆).map (MulAut.conj (g*t)).toMonoidHom : Subgroup G) : Set G) := by
  have hh := map_mono (f := (MulAut.conj g).toMonoidHom)
    (natural_partner_normalized m hn hz ht htn)
  rw [map_inf _ _ _ (MulAut.conj g).injective,
    map_equiv_normalizer_eq ⁅D.fullModule,L⁆ (MulAut.conj g),
    map_equiv_normalizer_eq ((⁅D.fullModule,L⁆).map (MulAut.conj t).toMonoidHom)
      (MulAut.conj g),←map_conj_mul] at hh
  exact hh

theorem natural_active_offender_contains_partner_of_normalizes
    (c : Configuration T D g) (m : SourceLinearThreeGeometry T D)
    (hsmall : subgroupCorank (D.fullModule.map (MulAut.conj g).toMonoidHom)
      (D.fullModule.map (MulAut.conj g).toMonoidHom ⊓ D.maximalLocal) ≤ 1)
    (hz : D.fullModule ⊓ centralizer (localOrbit T L : Set G) = ⊥)
    (hti : IsTISubgroup ⁅D.fullModule,L⁆)
    {t : G} (ht : t ∈ (T : Subgroup G)) (htn : t ∉ normalizer (L : Set G))
    (hactive : ¬ (⁅D.fullModule,L⁆).map (MulAut.conj g).toMonoidHom ≤
      centralizer ((⁅D.fullModule,L⁆ : Subgroup G) : Set G))
    (hAN : D.fullModule.map (MulAut.conj g).toMonoidHom ⊓ D.maximalLocal ≤
      normalizer ((⁅D.fullModule,L⁆ : Subgroup G) : Set G)) :
    (⁅D.fullModule,L⁆).map (MulAut.conj (g*t)).toMonoidHom ≤ D.maximalLocal := by
  let W := ⁅D.fullModule,L⁆
  let P := W.map (MulAut.conj g).toMonoidHom
  let Q := W.map (MulAut.conj (g*t)).toMonoidHom
  let V := D.fullModule.map (MulAut.conj g).toMonoidHom
  let A := V ⊓ D.maximalLocal
  let U := W ⊓ normalizer (P : Set G)
  let : IsElementaryAbelian 2 D.fullModule := m.full_eq_local.symm ▸ D.module_elementary
  let : IsElementaryAbelian 2 V := IsElementaryAbelian.map _
  have hgen : V = P ⊔ Q := by
    calc
      V = (W ⊔ W.map (MulAut.conj t).toMonoidHom).map
          (MulAut.conj g).toMonoidHom := congrArg (Subgroup.map
            (MulAut.conj g).toMonoidHom)
          (source_nonnormal_fullModule_eq_moved_pair D c.nonnormal ht (m.crossed t ht htn))
      _ = P ⊔ Q := (Subgroup.map_sup W (W.map (MulAut.conj t).toMonoidHom)
          (MulAut.conj g).toMonoidHom).trans
        (congrArg (fun H : Subgroup G => P ⊔ H) (map_conj_mul W g t).symm)
  have hPV : P ≤ V := le_sup_left.trans_eq hgen.symm
  have hQV : Q ≤ V := le_sup_right.trans_eq hgen.symm
  obtain ⟨hd,hA,hAc,hUc⟩ := natural_active_pair_normalizers c m hsmall hz hti hactive
  have hi : A.relIndex V = 2 := by
    have hi : A.relIndex V ≤ 2 := by
      change (V ⊓ D.maximalLocal).relIndex V ≤ 2
      have he : (V ⊓ D.maximalLocal).relIndex V =
          2 ^ subgroupCorank V (V ⊓ D.maximalLocal) := by
        rw [subgroupCorank_eq_quotient_finrank, inf_relIndex_left,
          relIndex_eq_two_pow_quotient_finrank V D.maximalLocal]
        congr 1
        rw [inf_subgroupOf_left]
      exact he.le.trans (Nat.pow_le_pow_right (by decide) hsmall)
    have hi0 : A.relIndex V ≠ 0 := index_ne_zero_of_finite
    have hi1 : A.relIndex V ≠ 1 := by
      intro hh
      have hPM := hPV.trans ((relIndex_eq_one.mp hh).trans inf_le_right)
      rw [inf_of_le_left hPM,card_map_of_injective (MulAut.conj g).injective,
        natural_moved_card_of_full_fixed_eq_bot m c.nonnormal hz] at hAc
      omega
    omega
  change Nat.card U = 4 at hUc
  have hUne : U ≠ ⊥ := by intro he; rw [he,card_bot] at hUc; omega
  obtain ⟨u,hu1⟩ := ne_bot_iff_exists_ne_one.mp hUne
  have hune : (u : G) ≠ 1 := fun hh => hu1 (Subtype.ext hh)
  have huM : (u : G) ∈ D.maximalLocal.map (MulAut.conj g).toMonoidHom :=
    natural_active_axis_le_conjugate_maximal c m hsmall hz hti hactive u.property
  have huQ : (u : G) ∈ normalizer (Q : Set G) :=
    natural_conjugate_partner_normalized m c.nonnormal hz ht htn ⟨huM,u.property.2⟩
  have hfix : ∀ a ∈ A, (MulAut.conj (u : G)) a = a := by
    intro a ha
    have hc := natural_active_offender_centralizes_axis_of_normalizes
      c m hsmall hz hti hactive hAN ha u u.property
    change (u : G)*a*(u : G)⁻¹=a
    rw [hc,mul_inv_cancel_right]
  have hmove : ∃ p ∈ P, (MulAut.conj (u : G)) p ≠ p := by
    by_contra! hh
    have hfull : P ⊓ centralizer ({(u : G)} : Set G) = P := by
      apply inf_eq_left.mpr
      intro p hp
      exact mem_centralizer_singleton_iff.mpr (mul_inv_eq_iff_eq_mul.mp (hh p hp)).symm
    have he := ti_pair_opposite_normalizer_eq_centralizer W P hd hti
      u.property.1 u.property.2 hune
    rw [hfull,←hA] at he
    rw [he,card_map_of_injective (MulAut.conj g).injective,
      natural_moved_card_of_full_fixed_eq_bot m c.nonnormal hz] at hAc
    omega
  have hWB : Disjoint W (W.map (MulAut.conj t).toMonoidHom) := by
    apply disjoint_iff.mpr
    exact bot_unique ((inf_le_inf_left W (m.crossed t ht htn)).trans_eq
      (moved_fixed_eq_bot_of_full_fixed_eq_bot m c.nonnormal hz))
  have hPQ : Disjoint P Q := by
    change Disjoint (W.map (MulAut.conj g).toMonoidHom)
      (W.map (MulAut.conj (g*t)).toMonoidHom)
    rw [map_conj_mul]
    exact disjoint_map (MulAut.conj g).injective hWB
  have hQA : Q ≤ A := fixed_hyperplane_partner V A P Q (MulAut.conj (u : G))
    hPV hQV hi hPQ
    (conjugate_eq_of_mem_normalizer _ u.property.2).le
    (conjugate_eq_of_mem_normalizer _ huQ).le hfix hmove
  exact hQA.trans inf_le_right

theorem natural_active_partner_not_le_maximal
    (c : Configuration T D g) (m : SourceLinearThreeGeometry T D)
    (hsmall : subgroupCorank (D.fullModule.map (MulAut.conj g).toMonoidHom)
      (D.fullModule.map (MulAut.conj g).toMonoidHom ⊓ D.maximalLocal) ≤ 1)
    (hz : D.fullModule ⊓ centralizer (localOrbit T L : Set G) = ⊥)
    (hti : IsTISubgroup ⁅D.fullModule,L⁆)
    {t : G} (ht : t ∈ (T : Subgroup G)) (htn : t ∉ normalizer (L : Set G))
    (hactive : ¬ (⁅D.fullModule,L⁆).map (MulAut.conj g).toMonoidHom ≤
      centralizer ((⁅D.fullModule,L⁆ : Subgroup G) : Set G)) :
    ¬ (⁅D.fullModule,L⁆).map (MulAut.conj (g*t)).toMonoidHom ≤ D.maximalLocal := by
  let W := ⁅D.fullModule,L⁆
  let P := W.map (MulAut.conj g).toMonoidHom
  let Q := W.map (MulAut.conj (g*t)).toMonoidHom
  let V := D.fullModule.map (MulAut.conj g).toMonoidHom
  let M := D.maximalLocal
  let := source_full_moved_elementary D
  let : IsElementaryAbelian 2 Q := IsElementaryAbelian.map _
  intro hQM
  have htM : t ∈ M := le_normalizer_componentOrbit L T ht
  have hfull : D.fullModule.map (MulAut.conj (g*t)).toMonoidHom = V := by
    rw [map_conj_mul,conjugate_eq_of_mem_normalizer D.fullModule
      (D.maximalLocal_normalizes_fullModule htM)]
  have hconjM : M.map (MulAut.conj (g*t)).toMonoidHom = M.map (MulAut.conj g).toMonoidHom := by
    rw [map_conj_mul,conjugate_eq_of_mem_normalizer _ (M.le_normalizer htM)]
  have hQV : Q ≤ V := by
    rw [←hfull]
    exact map_mono (le_normalizer_iff_commutator_le_left.mp
      (((le_componentOrbit L T).trans (localOrbit T L).le_normalizer).trans
        D.maximalLocal_normalizes_fullModule))
  have hdis : Disjoint W Q := disjoint_iff.mpr (bot_unique
    ((inf_le_inf_left W hQV).trans_eq
      (natural_active_moved_inf_full_conjugate_eq_bot c m hsmall hz hti hactive)))
  have c' := configuration_right_mul c htM
  have hs : subgroupCorank (D.fullModule.map (MulAut.conj (g*t)).toMonoidHom)
      (D.fullModule.map (MulAut.conj (g*t)).toMonoidHom ⊓ D.maximalLocal) ≤ 1 := by
    simpa only [hfull] using hsmall
  have hQN : Q ≤ normalizer (W : Set G) := by
    have hh := (natural_offender_geometry c' m hs hdis.eq_bot).1
    simpa only [inf_of_le_left hQM] using hh
  have hQW : Nat.card Q = Nat.card W := card_map_of_injective (MulAut.conj (g*t)).injective
  have hQC : Q ≤ centralizer (W : Set G) :=
    ti_pair_commute_of_full_normalizer Q W hdis.symm (hti.map_equiv (MulAut.conj (g*t)))
      hti hQW (inf_of_le_left hQN)
  have hne : Q ≠ ⊥ := by
    intro he
    have hh := hQW.trans (natural_moved_card_of_full_fixed_eq_bot m c.nonnormal hz)
    rw [he,card_bot] at hh
    omega
  obtain ⟨q,hq1⟩ := ne_bot_iff_exists_ne_one.mp hne
  obtain ⟨w,hw,he⟩ := q.property
  have hw1 : w ≠ 1 := by
    intro hh
    have hq : (q : G) = 1 := he.symm.trans (by simp only [hh,map_one])
    exact hq1 (Subtype.ext hq)
  have hcent : centralizer ({(q : G)} : Set G) ≤ M.map (MulAut.conj g).toMonoidHom := by
    rw [←he]
    change centralizer ({(MulAut.conj (g*t)) w} : Set G) ≤ _
    rw [←CentralizerSmallKernelTransport.map_centralizer (MulAut.conj (g*t)) w]
    exact (map_mono (c.pointCentralizers w hw hw1)).trans_eq hconjM
  have hWM : W ≤ M.map (MulAut.conj g).toMonoidHom := by
    intro w hw
    apply hcent
    exact mem_centralizer_singleton_iff.mpr (hQC q.property w hw)
  have hWQ : W ≤ normalizer (Q : Set G) :=
    (le_centralizer_iff.mp hQC).trans (Subgroup.centralizer_le_normalizer _)
  have hWN : W ≤ normalizer (P : Set G) := by
    have hh := natural_conjugate_partner_normalized (g := g*t) m c.nonnormal hz
      ((T : Subgroup G).inv_mem ht) (by simpa only [inv_mem_iff] using htn)
    simp only [mul_inv_cancel_right] at hh
    change M.map (MulAut.conj (g*t)).toMonoidHom ⊓ normalizer (Q : Set G) ≤
      normalizer (P : Set G) at hh
    rw [hconjM] at hh
    exact (le_inf hWM hWQ).trans hh
  have hUc := (natural_active_pair_normalizers c m hsmall hz hti hactive).2.2.2
  rw [inf_of_le_left hWN,natural_moved_card_of_full_fixed_eq_bot m c.nonnormal hz] at hUc
  omega

theorem natural_active_exists_swapping_offender
    (c : Configuration T D g) (m : SourceLinearThreeGeometry T D)
    (hsmall : subgroupCorank (D.fullModule.map (MulAut.conj g).toMonoidHom)
      (D.fullModule.map (MulAut.conj g).toMonoidHom ⊓ D.maximalLocal) ≤ 1)
    (hz : D.fullModule ⊓ centralizer (localOrbit T L : Set G) = ⊥)
    (hti : IsTISubgroup ⁅D.fullModule,L⁆)
    {t : G} (ht : t ∈ (T : Subgroup G)) (htn : t ∉ normalizer (L : Set G))
    (hactive : ¬ (⁅D.fullModule,L⁆).map (MulAut.conj g).toMonoidHom ≤
      centralizer ((⁅D.fullModule,L⁆ : Subgroup G) : Set G)) :
    ∃ d ∈ D.fullModule.map (MulAut.conj g).toMonoidHom ⊓ D.maximalLocal,
      (⁅D.fullModule,L⁆).map (MulAut.conj d).toMonoidHom =
        (⁅D.fullModule,L⁆).map (MulAut.conj t).toMonoidHom := by
  have hn : ¬ D.fullModule.map (MulAut.conj g).toMonoidHom ⊓ D.maximalLocal ≤
      normalizer ((⁅D.fullModule,L⁆ : Subgroup G) : Set G) := fun hh =>
    natural_active_partner_not_le_maximal c m hsmall hz hti ht htn hactive
      (natural_active_offender_contains_partner_of_normalizes c m hsmall hz hti ht htn hactive hh)
  obtain ⟨d,hd,hdn⟩ := SetLike.not_le_iff_exists.mp hn
  refine ⟨d,hd,?_⟩
  have hdL : L.map (MulAut.conj d).toMonoidHom ≠ L := by
    intro he
    apply hdn
    apply mem_normalizer_iff_map_conj_eq.mpr
    change (⁅D.fullModule,L⁆).map (MulAut.conj d).toMonoidHom = ⁅D.fullModule,L⁆
    rw [map_conj_commutator,conjugate_eq_of_mem_normalizer D.fullModule
      (D.maximalLocal_normalizes_fullModule hd.2),he]
  have he := (source_nonnormal_maximal_pair D c.nonnormal ht htn d hd.2).resolve_left hdL
  rw [map_conj_commutator,conjugate_eq_of_mem_normalizer D.fullModule
    (D.maximalLocal_normalizes_fullModule hd.2),he,map_conj_commutator,
    conjugate_eq_of_mem_normalizer D.fullModule
      (D.maximalLocal_normalizes_fullModule (le_normalizer_componentOrbit L T ht))]

end CFSG.Quasithin.Chapter10.SmallOffender.NaturalCorank
