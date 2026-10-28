module
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReplacement.Contracts
public import CFSG.Quasithin.Chapter10.SourceNonnormalPairAction
public import Theory.GroupTheory.TwoFixedLinesIrreducible
public import Theory.GroupTheory.DisjointCommutingProduct

/-!
# Fixed vectors in the original exchanged linear-three factors

The maximal local group permutes the two moved factors. Their intersection
is invariant and centralizes the first component, hence its whole Sylow
orbit. When the full fixed part vanishes, the factors are therefore disjoint.
A nonidentity T-fixed vector exists in their elementary product by the
p-group fixed-point theorem. Its unique coordinates are fixed by N_T(L),
and exchange forces both coordinates to be nonidentity. Their product is
the central involution used in the original centralizer construction.

The point-centralizer hypothesis of the survivor also controls the
centralizer of the literal V_z. The containments V,V_z ≤ C_G(z) are proved
directly, without assuming the later two-core conclusion.

Source: Aschbacher--Smith 10.2.10--11 and the notation following 10.3.2,
printed pp.753--756. The zero fixed-part premise remains the independent
source theorem 10.3.1; no claim below discharges that premise.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter10.SourceLinearThreeReplacement
open Chapter3.Section02
open scoped IsMulCommutative
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  {D : FundamentalSetup KnownSimple.IsKnownSimple T L}
  (s : SourceLinearThreeSurvivor T D)

include s

/-- The specified exchange witnesses the original nonnormal case. -/
theorem survivor_nonnormal : ¬ (T : Subgroup G) ≤ normalizer (L : Set G) :=
  fun h => s.exchange_moves (h s.exchange_mem)

/-- The first moved factor lies in the original full module. -/
theorem survivor_moved_le : ⁅D.fullModule,L⁆ ≤ D.fullModule := by
  exact le_sup_left.trans_eq s.generated.symm

/-- The exchanged moved factor lies in the same full module. -/
theorem survivor_partner_le :
    (⁅D.fullModule,L⁆).map (MulAut.conj s.exchange).toMonoidHom ≤ D.fullModule := by
  exact le_sup_right.trans_eq s.generated.symm

/-- The whole original maximal local group permutes the two moved factors. -/
theorem survivor_moved_pair (g : G) (hg : g ∈ D.maximalLocal) :
    (⁅D.fullModule,L⁆).map (MulAut.conj g).toMonoidHom = ⁅D.fullModule,L⁆ ∨
    (⁅D.fullModule,L⁆).map (MulAut.conj g).toMonoidHom =
      (⁅D.fullModule,L⁆).map (MulAut.conj s.exchange).toMonoidHom := by
  have hV (m : G) (hm : m ∈ D.maximalLocal) :
      D.fullModule.map (MulAut.conj m).toMonoidHom = D.fullModule :=
    mem_normalizer_iff_map_conj_eq.mp (D.maximalLocal_normalizes_fullModule hm)
  rw [map_commutator, hV g hg, map_commutator,
    hV s.exchange (le_normalizer_componentOrbit L T s.exchange_mem)]
  rcases source_nonnormal_maximal_pair D (survivor_nonnormal s)
      s.exchange_mem s.exchange_moves g hg with h | h
  · exact Or.inl (congrArg (fun A : Subgroup G => ⁅D.fullModule,A⁆) h)
  · exact Or.inr (congrArg (fun A : Subgroup G => ⁅D.fullModule,A⁆) h)

private theorem partner_pair (g : G) (hg : g ∈ D.maximalLocal) :
    ((⁅D.fullModule,L⁆).map (MulAut.conj s.exchange).toMonoidHom).map
        (MulAut.conj g).toMonoidHom = ⁅D.fullModule,L⁆ ∨
    ((⁅D.fullModule,L⁆).map (MulAut.conj s.exchange).toMonoidHom).map
        (MulAut.conj g).toMonoidHom =
      (⁅D.fullModule,L⁆).map (MulAut.conj s.exchange).toMonoidHom := by
  have he : (MulAut.conj g).toMonoidHom.comp (MulAut.conj s.exchange).toMonoidHom =
      (MulAut.conj (g * s.exchange)).toMonoidHom := by
    ext x
    simp [MulAut.conj_apply, mul_assoc]
  rw [map_map, he]
  exact survivor_moved_pair s _
    (D.maximalLocal.mul_mem hg (le_normalizer_componentOrbit L T s.exchange_mem))

/-- The intersection of the exchanged factors belongs to the full fixed part. -/
theorem survivor_pair_intersection_fixed :
    ⁅D.fullModule,L⁆ ⊓ (⁅D.fullModule,L⁆).map (MulAut.conj s.exchange).toMonoidHom ≤
      D.fullModule ⊓ centralizer (localOrbit T L : Set G) := by
  let A := ⁅D.fullModule,L⁆
  let B := A.map (MulAut.conj s.exchange).toMonoidHom
  let I := A ⊓ B
  have hn : D.maximalLocal ≤ normalizer (I : Set G) := by
    intro g hg
    apply mem_normalizer_iff_map_conj_eq.mpr
    change (A ⊓ B).map (MulAut.conj g).toMonoidHom = A ⊓ B
    rw [map_inf _ _ _ (MulAut.conj g).injective]
    rcases survivor_moved_pair s g hg with ha | ha <;>
      rcases partner_pair s g hg with hb | hb
    · have he : A = B := map_injective (MulAut.conj g).injective (ha.trans hb.symm)
      change A.map _ = A at ha
      change B.map _ = A at hb
      simp only [hb, he]
    · rw [ha, hb]
    · rw [ha, hb, inf_comm]
    · have he : A = B := map_injective (MulAut.conj g).injective (ha.trans hb.symm)
      change A.map _ = B at ha
      change B.map _ = B at hb
      simp only [hb, he]
  have hLC : L ≤ centralizer (I : Set G) :=
    le_centralizer_iff.mp (inf_le_right.trans s.crossed)
  have hTC : (T : Subgroup G) ≤ normalizer (centralizer (I : Set G) : Set G) :=
    ((le_normalizer_componentOrbit L T).trans hn).trans
      (normalizer_le_normalizer_centralizer _)
  exact le_inf (inf_le_left.trans (survivor_moved_le s))
    (le_centralizer_iff.mpr (iSup_conjugates_le_of_le_normalizer _ _ _ hLC hTC))

/-- Vanishing of the full fixed part gives an internal direct product. -/
theorem survivor_pair_disjoint
    (hz : D.fullModule ⊓ centralizer (localOrbit T L : Set G) = ⊥) :
    Disjoint ⁅D.fullModule,L⁆
      ((⁅D.fullModule,L⁆).map (MulAut.conj s.exchange).toMonoidHom) :=
  disjoint_iff.mpr (bot_unique ((survivor_pair_intersection_fixed s).trans_eq hz))

/-- The outside-M intersection conclusion of 10.2.10(1) supplies the full
TI conclusion once the fixed part is zero. The original M-action, rather
than an assumed permutation action on abstract factors, is used here. -/
theorem survivor_moved_ti_of_fixed_of_outside
    (hz : D.fullModule ⊓ centralizer (localOrbit T L : Set G) = ⊥)
    (hout : ∀ g ∉ D.maximalLocal,
      ⁅D.fullModule,L⁆ ⊓ (⁅D.fullModule,L⁆).map (MulAut.conj g).toMonoidHom = ⊥) :
    ∀ g : G,
      ⁅D.fullModule,L⁆ ⊓ (⁅D.fullModule,L⁆).map (MulAut.conj g).toMonoidHom = ⊥ ∨
      (⁅D.fullModule,L⁆).map (MulAut.conj g).toMonoidHom = ⁅D.fullModule,L⁆ := by
  intro g
  rcases map_conj_eq_or_inf_eq_bot_of_conj_pair D.maximalLocal ⁅D.fullModule,L⁆
    ((⁅D.fullModule,L⁆).map (MulAut.conj s.exchange).toMonoidHom)
    (survivor_moved_pair s) (survivor_pair_disjoint s hz).eq_bot hout g with h | h
  · exact Or.inr h
  · exact Or.inl h

/-- The literal stabilizer N_T(L) preserves the first moved factor. -/
theorem survivor_stabilizer_normalizes_moved :
    (T : Subgroup G) ⊓ normalizer (L : Set G) ≤
      normalizer ((⁅D.fullModule,L⁆ : Subgroup G) : Set G) := by
  intro g hg
  apply mem_normalizer_iff_map_conj_eq.mpr
  rw [map_commutator, s.full_eq_local,
    mem_normalizer_iff_map_conj_eq.mp (D.sylow_normalizes_module hg.1),
    mem_normalizer_iff_map_conj_eq.mp hg.2]

/-- The same stabilizer preserves the exchanged factor. -/
theorem survivor_stabilizer_normalizes_partner :
    (T : Subgroup G) ⊓ normalizer (L : Set G) ≤ normalizer
      (((⁅D.fullModule,L⁆).map (MulAut.conj s.exchange).toMonoidHom) : Set G) := by
  intro g hg
  apply mem_normalizer_iff_map_conj_eq.mpr
  rcases partner_pair s g (le_normalizer_componentOrbit L T hg.1) with h | h
  · have ha := mem_normalizer_iff_map_conj_eq.mp (survivor_stabilizer_normalizes_moved s hg)
    have he := map_injective (MulAut.conj g).injective (h.trans ha.symm)
    exact h.trans he.symm
  · exact h

/-- Construct the two nonidentity stabilizer-fixed vectors and their
central involution product. Only the earlier fixed-part conclusion remains
explicit; the vectors and their centrality are not additional hypotheses. -/
theorem exists_survivor_diagonal
    (hz : D.fullModule ⊓ centralizer (localOrbit T L : Set G) = ⊥) :
    ∃ a b : G, a ∈ ⁅D.fullModule,L⁆ ∧
      b ∈ (⁅D.fullModule,L⁆).map (MulAut.conj s.exchange).toMonoidHom ∧
      a ≠ 1 ∧ b ≠ 1 ∧
      a ∈ centralizer (((T : Subgroup G) ⊓ normalizer (L : Set G) : Subgroup G) : Set G) ∧
      b ∈ centralizer (((T : Subgroup G) ⊓ normalizer (L : Set G) : Subgroup G) : Set G) ∧
      a * b ∈ centerIn (T : Subgroup G) ∧ orderOf (a * b) = 2 := by
  let A := ⁅D.fullModule,L⁆
  let B := A.map (MulAut.conj s.exchange).toMonoidHom
  let V := D.fullModule
  let : IsElementaryAbelian 2 V := by
    change IsElementaryAbelian 2 D.fullModule
    rw [s.full_eq_local]
    exact D.module_elementary
  have hAV : A ≤ V := survivor_moved_le s
  have hBV : B ≤ V := survivor_partner_le s
  have hd : Disjoint A B := survivor_pair_disjoint s hz
  have hc : A ≤ centralizer (B : Set G) := by
    intro a ha b hb
    exact congrArg Subtype.val (mul_comm (⟨b,hBV hb⟩ : V) ⟨a,hAV ha⟩)
  have hTV : (T : Subgroup G) ≤ normalizer (V : Set G) :=
    (le_normalizer_componentOrbit L T).trans D.maximalLocal_normalizes_fullModule
  have hn : V ≠ ⊥ := by
    change D.fullModule ≠ ⊥
    rw [s.full_eq_local]
    exact D.module_ne_bot
  have hf := inf_centralizer_ne_bot_of_pGroups (T : Subgroup G) V
    T.isPGroup' (IsElementaryAbelian.isPGroup 2 V) hTV hn
  obtain ⟨z,hzne⟩ := ne_bot_iff_exists_ne_one.mp hf
  have hzne' : (z : G) ≠ 1 := fun h => hzne (Subtype.ext h)
  obtain ⟨e,he⟩ := exists_mulEquiv_prod_sup_of_disjoint_of_commuting A B hd hc
  have hzAB : (z : G) ∈ A ⊔ B := by
    change (z:G) ∈ ⁅D.fullModule,L⁆ ⊔
      (⁅D.fullModule,L⁆).map (MulAut.conj s.exchange).toMonoidHom
    rw [← s.generated]
    exact z.property.1
  obtain ⟨⟨a,b⟩,hab⟩ := e.surjective ⟨z,hzAB⟩
  have hab' : (a:G) * (b:G) = (z:G) := (he a b).symm.trans (congrArg Subtype.val hab)
  have hfix (t : G) (ht : t ∈ (T : Subgroup G)) : (MulAut.conj t) (z:G) = (z:G) := by
    change t * (z:G) * t⁻¹ = (z:G)
    rw [z.property.2 t ht, mul_inv_cancel_right]
  have hane : (a:G) ≠ 1 := by
    intro ha
    have hzb : (z:G) ∈ B := by
      have hbz : (b:G) = (z:G) := by simpa only [ha, one_mul] using hab'
      exact hbz ▸ b.property
    have hza : (z:G) ∈ A := by
      obtain ⟨x,hx,hxz⟩ := hzb
      have hh : x = (z:G) := (MulAut.conj s.exchange).injective
        (hxz.trans (hfix s.exchange s.exchange_mem).symm)
      exact hh ▸ hx
    exact hzne' (mem_bot.mp (hd.eq_bot ▸ (show (z:G) ∈ A ⊓ B from ⟨hza,hzb⟩)))
  have hbne : (b:G) ≠ 1 := by
    intro hb
    have hza : (z:G) ∈ A := by
      have haz : (a:G) = (z:G) := by simpa only [hb, mul_one] using hab'
      exact haz ▸ a.property
    have hzb : (z:G) ∈ B := by
      have hh := mem_map_of_mem (MulAut.conj s.exchange).toMonoidHom hza
      change (MulAut.conj s.exchange) (z:G) ∈ B at hh
      rwa [hfix s.exchange s.exchange_mem] at hh
    exact hzne' (mem_bot.mp (hd.eq_bot ▸ (show (z:G) ∈ A ⊓ B from ⟨hza,hzb⟩)))
  have hfixed (t : G) (ht : t ∈ (T : Subgroup G) ⊓ normalizer (L : Set G)) :
      (MulAut.conj t) (a:G) = a ∧ (MulAut.conj t) (b:G) = b := by
    have ha := (mem_normalizer_iff.mp (survivor_stabilizer_normalizes_moved s ht) a).mp a.property
    have hb := (mem_normalizer_iff.mp (survivor_stabilizer_normalizes_partner s ht) b).mp b.property
    have hh : (MulAut.conj t) (a:G) * (MulAut.conj t) (b:G) = (a:G) * (b:G) := by
      rw [← map_mul, hab', hfix t ht.1]
    have hp : ((⟨(MulAut.conj t) (a:G),ha⟩ : A),(⟨(MulAut.conj t) (b:G),hb⟩ : B)) =
        (a,b) := mul_injective_of_disjoint hd hh
    exact ⟨congrArg (fun p : A × B => (p.1:G)) hp,
      congrArg (fun p : A × B => (p.2:G)) hp⟩
  refine ⟨a,b,a.property,b.property,hane,hbne,?_,?_,?_,?_⟩
  · intro t ht
    exact mul_inv_eq_iff_eq_mul.mp (hfixed t ht).1
  · intro t ht
    exact mul_inv_eq_iff_eq_mul.mp (hfixed t ht).2
  · rw [hab']
    exact ⟨D.module_le_sylow (s.full_eq_local ▸ z.property.1),z.property.2⟩
  · rw [hab']
    exact orderOf_eq_prime_iff.mpr
      ⟨elemPow_eq_one_of_isElementaryAbelian (p := 2) (z:G) z.property.1,hzne'⟩

/-- The required V_z-centralizer bound follows from the first fixed vector
and the survivor's original point-centralizer control. -/
theorem centralizerModule_centralizer_le {a b : G}
    (ha : a ∈ ⁅D.fullModule,L⁆) (hne : a ≠ 1) :
    centralizer ({a*b} : Set G) ⊓ centralizer (centralizerModule a b : Set G) ≤ D.maximalLocal := by
  apply inf_le_right.trans
  apply le_trans (centralizer_le ?_) (s.pointCentralizers a ha hne)
  exact Set.singleton_subset_iff.mpr (le_conjugateSpanBy (zpowers a ⊔ zpowers b)
    (centralizer ({a*b} : Set G)) (mem_sup_left (mem_zpowers a)))

/-- The whole full module lies in the centralizer of each such product. -/
theorem survivor_full_le_diagonal_centralizer {a b : G}
    (ha : a ∈ ⁅D.fullModule,L⁆)
    (hb : b ∈ (⁅D.fullModule,L⁆).map (MulAut.conj s.exchange).toMonoidHom) :
    D.fullModule ≤ centralizer ({a*b} : Set G) := by
  let : IsElementaryAbelian 2 D.fullModule := s.full_eq_local.symm ▸ D.module_elementary
  have hz : a*b ∈ D.fullModule :=
    D.fullModule.mul_mem (survivor_moved_le s ha) (survivor_partner_le s hb)
  intro x hx
  apply mem_centralizer_singleton_iff.mpr
  exact congrArg Subtype.val (mul_comm (⟨x,hx⟩ : D.fullModule) ⟨a*b,hz⟩)

/-- The actual E-conjugate span lies in its acting centralizer. -/
theorem survivor_centralizerModule_le {a b : G}
    (ha : a ∈ ⁅D.fullModule,L⁆)
    (hb : b ∈ (⁅D.fullModule,L⁆).map (MulAut.conj s.exchange).toMonoidHom) :
    centralizerModule a b ≤ centralizer ({a*b} : Set G) := by
  apply conjugateSpanBy_le_self
  have hv := survivor_full_le_diagonal_centralizer s ha hb
  exact sup_le (zpowers_le.mpr (hv (survivor_moved_le s ha)))
    (zpowers_le.mpr (hv (survivor_partner_le s hb)))

end CFSG.Quasithin.Chapter10.SourceLinearThreeReplacement
