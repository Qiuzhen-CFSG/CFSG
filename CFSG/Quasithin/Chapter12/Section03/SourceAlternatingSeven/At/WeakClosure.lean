module

public import CFSG.Quasithin.Chapter12.Section03.SourceAlternatingSeven.WeakClosure
public import CFSG.Quasithin.Chapter12.Section02.StructuralSource.At
public import CFSG.Quasithin.Chapter12.Section03.SourceAlternatingSeven.At.TerminalContainment
public import CFSG.Quasithin.Chapter12.Section03.SourceAlternatingSeven.At.WeakClosureKernel

/-!
# The repaired A₇ weak-closure bound, including the simplex case

The checked intersection theorem gives r≥3. For a noncentralizing actor
A=N_{Vᵍ}(V) of corank at most one, a weight-two displacement first excludes
V≤N(Vᵍ). Hence its centralizer kernel has rank at most three, and its actual
S₇ image has order four or eight. Every hyperplane of A has corank at most
two in Vᵍ, so its full centralizer normalizes Vᵍ.

An image of order eight gives a weight-two commutator in V∩Vᵍ, contradicting
the intersection weights. An image of order four forces a rank-three kernel;
its local pointwise-stabilizer equality contradicts growth of fixed vectors
on a hyperplane. Thus all these actors centralize V, proving W₁(T,V)≤C_T(V)
and w>1 without the incorrect rank-four assertion or ambient simplex control.
The final application discharges the r,w premises of the genuine E.3.35
consumer, proving 12.3.11 conditional only on the earlier LocalAnalysis.

Source: Aschbacher--Smith, 12.3.9--11, printed pp.810--811, and E.3.3--4,
E.3.23. The parent source task constructs LocalAnalysis; neither that result
nor the full A₇ exclusion is assumed proved here.
The versions in this extension require only `Structural1222At` and
`Theorem1222ModulesAt` at the original G,T. Every overcomponent is treated
in that same ambient group with that same Sylow subgroup. The original
universal declarations and all shared quotient/action records are preserved.
-/

public section

open Subgroup Theory.GroupTheory

namespace CFSG.Quasithin.Chapter12.Section03.SourceAlternatingSeven

open Section02 ChapterE BinarySevenCode

universe u

variable {G : Type u} [Group G] [Finite G]

variable {T : Sylow 2 G} {L V : Subgroup G}

variable (S : Setup T L V) (D : S.LocalAnalysis)

variable (structural : Structural1222At KnownSimple.IsKnownSimple T)

private theorem displacement_ne_one_at (g : G) (a : offenderNormalizer V g) (v : V)
    (hw : weight (D.model.coordinates (actorDisplacement g a v)).toAdd.val = 2) :
    actorDisplacement g a v ≠ 1 := by
  intro he
  simp [he, weight] at hw

omit [Finite G] in

private theorem displacement_mem_conjugate_at (g : G) (a : offenderNormalizer V g) (v : V)
    (hv : v.val ∈ normalizer (V.map (MulAut.conj g).toMonoidHom : Set G)) :
    (actorDisplacement g a v).val ∈ V.map (MulAut.conj g).toMonoidHom := by
  have hc : v.val * a.val⁻¹ * v.val⁻¹ ∈ V.map (MulAut.conj g).toMonoidHom :=
    (mem_normalizer_iff.mp hv a.val⁻¹).mp (inv_mem a.property.1)
  have hh := (V.map (MulAut.conj g).toMonoidHom).mul_mem a.property.1 hc
  simpa only [actorDisplacement_val, mul_assoc] using hh

include S D structural in

private theorem no_weight_two_displacement_at (g : G) (hg : g ∉ normalizer (V : Set G))
    (a : offenderNormalizer V g) (v : V)
    (hv : v.val ∈ normalizer (V.map (MulAut.conj g).toMonoidHom : Set G))
    (hw : weight (D.model.coordinates (actorDisplacement g a v)).toAdd.val = 2) : False := by
  have hn := displacement_ne_one_at S D g a v hw
  have hfour := intersection_weight_four_at S D structural hg
    ⟨(actorDisplacement g a v).property, displacement_mem_conjugate_at g a v hv⟩
    (fun he => hn (Subtype.ext he))
  rw [hw] at hfour
  contradiction

include S D structural in

theorem actor_not_reverse_normalizes_at (g : G)
    (hAC : ¬ offenderNormalizer V g ≤ centralizer (V : Set G)) :
    ¬ V ≤ normalizer (V.map (MulAut.conj g).toMonoidHom : Set G) := by
  let _ := S.chosen.elementary
  have hg : g ∉ normalizer (V : Set G) := by
    intro hg
    have hW : V.map (MulAut.conj g).toMonoidHom = V := mem_normalizer_iff_map_conj_eq.mp hg
    apply hAC
    exact (show offenderNormalizer V g ≤ V by
      simpa only [offenderNormalizer,hW] using
        (inf_le_left : V ⊓ normalizer (V : Set G) ≤ V)).trans
      (le_centralizer_iff_isMulCommutative.mpr inferInstance)
  obtain ⟨a,ha,hn⟩ := SetLike.not_le_iff_exists.mp hAC
  have hp : D.model.permutation ⟨a,ha.2⟩ ≠ 1 :=
    fun he => hn ((actor_permutation_eq_one_iff S D _).mp he)
  obtain ⟨v,hv⟩ := actor_weight_two S D g ⟨a,ha⟩ hp
  intro hVN
  exact no_weight_two_displacement_at S D structural g hg ⟨a,ha⟩ v (hVN v.property) hv

private theorem elementary_card_at (H : Subgroup G) [IsElementaryAbelian 2 H] :
    Nat.card H = 2 ^ Nat.log 2 (Nat.card H) := by
  obtain ⟨n,hn⟩ := (IsElementaryAbelian.isPGroup 2 H).exists_card_eq
  rw [hn, Nat.log_pow (by decide)]

include S D structural in

theorem actor_small_corank_orders_at (g : G)
    (hc : subgroupCorank (V.map (MulAut.conj g).toMonoidHom) (offenderNormalizer V g) ≤ 1)
    (hAC : ¬ offenderNormalizer V g ≤ centralizer (V : Set G)) :
    32 ≤ Nat.card (offenderNormalizer V g) ∧
    Nat.card (V.map (MulAut.conj g).toMonoidHom ⊓ centralizer (V : Set G) : Subgroup G) ≤ 8 ∧
    (Nat.card (actorImage S D g) = 4 ∨ Nat.card (actorImage S D g) = 8) := by
  let _ := S.chosen.elementary
  let W := V.map (MulAut.conj g).toMonoidHom
  let K := W ⊓ centralizer (V : Set G)
  let _ : IsElementaryAbelian 2 W := IsElementaryAbelian.map _
  let _ : IsElementaryAbelian 2 K := IsElementaryAbelian.of_le (show K ≤ W from inf_le_left)
  let _ : IsElementaryAbelian 2 (offenderNormalizer V g) :=
    IsElementaryAbelian.of_le (show offenderNormalizer V g ≤ W from inf_le_left)
  have hk := conjugate_centralizer_rank_le_three_at S D structural g
    (actor_not_reverse_normalizes_at S D structural g hAC)
  have hK : Nat.card K ≤ 8 := by
    rw [elementary_card_at K]
    exact pow_le_pow_right' (by decide : 1 ≤ 2) hk
  have hA : 32 ≤ Nat.card (offenderNormalizer V g) := by
    rw [subgroupCorank, ← log_card_sub_log_card_eq_log_relIndex _ _ (show offenderNormalizer V g ≤
      V.map (MulAut.conj g).toMonoidHom from inf_le_left),
      card_map_of_injective (MulAut.conj g).injective, D.model.log_card_eq_six] at hc
    rw [elementary_card_at (offenderNormalizer V g)]
    exact pow_le_pow_right' (by decide : 1 ≤ 2) (by omega : 5 ≤ _)
  have hprod := actor_card_kernel_mul_image S D g
  have hI := Representation.AlternatingSevenConjugatePair.ElementaryGeometry.elementary_card_le
    (actorImage_elementary S D g)
  let _ := actorImage_elementary S D g
  obtain ⟨n,hn⟩ := (IsElementaryAbelian.isPGroup 2 (actorImage S D g)).exists_card_eq
  have hn3 : n ≤ 3 := by
    rw [hn] at hI
    exact (Nat.pow_le_pow_iff_right (by decide : 1 < 2)).mp hI
  refine ⟨hA,hK,?_⟩
  interval_cases n
  · rw [hn] at hprod
    change Nat.card K * 1 = _ at hprod
    omega
  · rw [hn] at hprod
    change Nat.card K * 2 = _ at hprod
    omega
  · exact Or.inl hn
  · exact Or.inr hn

include S D structural in

theorem actor_hyperplane_centralizer_normalizes_at (g : G)
    (hc : subgroupCorank (V.map (MulAut.conj g).toMonoidHom) (offenderNormalizer V g) ≤ 1)
    {B : Subgroup G} (hBA : B ≤ offenderNormalizer V g)
    (hi : B.relIndex (offenderNormalizer V g) = 2) :
    centralizer (B : Set G) ≤ normalizer (V.map (MulAut.conj g).toMonoidHom : Set G) := by
  let _ := S.chosen.elementary
  let _ : IsElementaryAbelian 2 (V.map (MulAut.conj g).toMonoidHom) :=
    IsElementaryAbelian.map _
  apply conjugate_centralizer_normalizes_of_corank_le_two_at S D structural g
    (hBA.trans inf_le_left)
  rw [offender_corank_add hBA (show offenderNormalizer V g ≤
    V.map (MulAut.conj g).toMonoidHom from inf_le_left)]
  have hb : subgroupCorank (offenderNormalizer V g) B = 1 := by
    change Nat.log 2 (B.relIndex (offenderNormalizer V g)) = 1
    rw [hi]; decide
  omega

include S D structural in

theorem actor_centralizes_of_corank_le_one_at (g : G)
    (hc : subgroupCorank (V.map (MulAut.conj g).toMonoidHom) (offenderNormalizer V g) ≤ 1) :
    offenderNormalizer V g ≤ centralizer (V : Set G) := by
  by_contra hAC
  have hVN := actor_not_reverse_normalizes_at S D structural g hAC
  have hg : g ∉ normalizer (V : Set G) := by
    intro hg
    have hW : V.map (MulAut.conj g).toMonoidHom = V := mem_normalizer_iff_map_conj_eq.mp hg
    exact hVN (by rw [hW]; exact V.le_normalizer)
  obtain ⟨hA,hK,hfour | height⟩ := actor_small_corank_orders_at S D structural g hc hAC
  · let K := V.map (MulAut.conj g).toMonoidHom ⊓ centralizer (V : Set G)
    have hprod := actor_card_kernel_mul_image S D g
    rw [hfour] at hprod
    have hK8 : Nat.card K = 8 := by
      change Nat.card K ≤ 8 at hK
      change Nat.card K * 4 = _ at hprod
      omega
    have hrK : Nat.log 2 (Nat.card K) = 3 := by rw [hK8]; decide
    have hesc : ¬ centralizer (K : Set G) ≤
        normalizer (V.map (MulAut.conj g).toMonoidHom : Set G) := by
      intro hh
      exact hVN ((le_centralizer_iff.mpr (show K ≤ centralizer (V : Set G) from inf_le_right)).trans hh)
    have hfix := conjugate_rank_three_centralizer_at S D structural g
      (show K ≤ V.map (MulAut.conj g).toMonoidHom from inf_le_left) hrK hesc
    obtain ⟨B,hBA,hi,v,hv,hva⟩ := actor_four_hyperplane S D g hfour
    have hvN := actor_hyperplane_centralizer_normalizes_at S D structural g hc hBA hi hv
    have hvK : v.val ∈ centralizer (K : Set G) :=
      (le_centralizer_iff.mpr (show K ≤ centralizer (V : Set G) from inf_le_right)) v.property
    have hvW := hfix.le ⟨hvN,hvK⟩
    exact hva (centralizer_le (show offenderNormalizer V g ≤
      V.map (MulAut.conj g).toMonoidHom from inf_le_left) hvW)
  · obtain ⟨B,hBA,hi,a,v,hv,hw⟩ := actor_eight_hyperplane S D g height
    exact no_weight_two_displacement_at S D structural g hg a v
      (actor_hyperplane_centralizer_normalizes_at S D structural g hc hBA hi hv) hw

include S D structural in

theorem weakClosure_one_le_centralizer_at :
    indexedWeakClosure V (T : Subgroup G) 1 ≤ (T : Subgroup G) ⊓ centralizer (V : Set G) := by
  let _ := S.chosen.elementary
  apply le_inf (indexedWeakClosure_le _ _ _)
  rw [weakClosure_eq_sSup_gamma]
  apply sSup_le
  rintro A ⟨⟨g,hAW,hi⟩,hAT⟩
  have hAN : A ≤ offenderNormalizer V g := le_inf hAW
    (hAT.trans ((structural L S.hypothesis).2.2 V S.chosen).1)
  have hc : subgroupCorank (V.map (MulAut.conj g).toMonoidHom) (offenderNormalizer V g) ≤ 1 := by
    let _ : IsElementaryAbelian 2 (V.map (MulAut.conj g).toMonoidHom) :=
      IsElementaryAbelian.map _
    have h := offender_corank_add hAN (show offenderNormalizer V g ≤
      V.map (MulAut.conj g).toMonoidHom from inf_le_left)
    have hca : subgroupCorank (V.map (MulAut.conj g).toMonoidHom) A = 1 := by
      rw [subgroupCorank,hi,Nat.log_pow (by decide)]
    omega
  exact hAN.trans (actor_centralizes_of_corank_le_one_at S D structural g hc)

include S D structural in

theorem one_lt_globalW_at : (1 : ℕ∞) < globalW V (T : Subgroup G) := by
  let _ := S.chosen.elementary
  have hT : HypothesisE322 V T := ⟨S.chosen.ne_bot, S.chosen.le_sylow,
    ((structural L S.hypothesis).2.2 V S.chosen).1⟩
  by_contra hn
  have hw : globalW V (T : Subgroup G) ≤ 1 := le_of_not_gt hn
  have hfin : globalW V (T : Subgroup G) ≠ ⊤ := ne_top_of_le_ne_top (by simp) hw
  obtain ⟨A,⟨⟨g,hAW,hi⟩,hAT⟩,hAC⟩ := globalW_generator (ENat.natCast_toNat hfin).symm
  have hAN : A ≤ offenderNormalizer V g := le_inf hAW (hAT.trans hT.normalizes)
  have hc : subgroupCorank (V.map (MulAut.conj g).toMonoidHom) (offenderNormalizer V g) ≤ 1 := by
    let _ : IsElementaryAbelian 2 (V.map (MulAut.conj g).toMonoidHom) :=
      IsElementaryAbelian.map _
    have h := offender_corank_add hAN (show offenderNormalizer V g ≤
      V.map (MulAut.conj g).toMonoidHom from inf_le_left)
    have hca : subgroupCorank (V.map (MulAut.conj g).toMonoidHom) A =
        (globalW V (T : Subgroup G)).toNat := by
      rw [subgroupCorank,hi,Nat.log_pow (by decide)]
    have hnat : (globalW V (T : Subgroup G)).toNat ≤ 1 :=
      ENat.toNat_le_toNat hw (by simp)
    omega
  exact hAC (hAN.trans (actor_centralizes_of_corank_le_one_at S D structural g hc))

include S D structural

theorem weakClosure_bounds_at :
    (1 : ℕ∞) < globalR V ∧ (1 : ℕ∞) < globalW V (T : Subgroup G) :=
  ⟨one_lt_globalR_at S D structural, one_lt_globalW_at S D structural⟩

omit D in

theorem source_weakClosure_bounds_at
    (localAnalysis_at : ∀ {L' V' : Subgroup G} (S' : Setup T L' V'), Nonempty S'.LocalAnalysis) :
    (1 : ℕ∞) < globalR V ∧ (1 : ℕ∞) < globalW V (T : Subgroup G) := by
  obtain ⟨D⟩ := localAnalysis_at S
  exact weakClosure_bounds_at S D structural

theorem generation_one_le_normalizer_of_localAnalysis_at {H : Subgroup G}
    (hTH : (T : Subgroup G) ≤ H) (hn : generationParameter H = 1) :
    H ≤ normalizer (L : Set G) :=
  generation_one_le_normalizer_at S structural hTH hn
    (one_lt_globalR_at S D structural) (one_lt_globalW_at S D structural)

end CFSG.Quasithin.Chapter12.Section03.SourceAlternatingSeven

