module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingOneProfile.OppositeSeeds

public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingOneProfile.CenterIdentities
public import Theory.ElementaryAbelian.Injective

/-!
# Separation of the neighboring-core intersection

The opposite seeds generate the alpha stabilizer modulo its two-core,
so they are transitive on its neighbors. They centralize the intersection
of the beta neighboring cores with the remote alpha core. At beta the
centralizer of the whole neighboring-core intersection is already
transitive. The faithful connected graph then forces the intersection
to be trivial. No tree hypothesis is required.

The resulting faithful map of Z₀ into the remote A₅ quotient makes Z₀
elementary of order at most four. This proves the opening separation and
elementary-layer arguments of (11.6) on the cubic A₅ branch. `MixedSeparation` applies it to the original reduced A₅/S₃ pair.
Source: Delgado--Goldschmidt--Stellmacher, *Groups and Graphs* (1985),
(11.5)--(11.6), printed p.172, using (3.2)(c), printed p.73.
-/

public noncomputable section
open Subgroup
open scoped Pointwise
namespace CFSG.Quasithin.ChapterF.Source.DGS85.CommutingOneProfile
open Subgroup.CosetGeometry.RankTwo Theory.GroupTheory.AmalgamGraph
variable {G : Type*} [Group G] {P : Fin 2 → Subgroup G} {B : Subgroup G}

private theorem elementary_small_of_a5_embedding {D : Type*} [Group D]
    (hp : IsPGroup 2 D) (f : D →* alternatingGroup (Fin 5)) (hf : Function.Injective f) :
    IsElementaryAbelian 2 D ∧ Nat.card D ≤ 4 := by
  let : MulAction D (Fin 5) := MulAction.compHom _ ((alternatingGroup (Fin 5)).subtype.comp f)
  obtain ⟨i,hi⟩ := hp.nonempty_fixed_point_of_prime_not_dvd_card (Fin 5) (by simp)
  let f₀ : D →* MulAction.stabilizer (alternatingGroup (Fin 5)) i :=
    f.codRestrict _ (fun x => hi x)
  have hf₀ : Function.Injective f₀ := fun _ _ he => hf (congrArg Subtype.val he)
  let e := AlternatingSix.SmallIndex.pointEquiv i
  let f₁ := e.toMonoidHom.comp f₀
  have hf₁ : Function.Injective f₁ := e.injective.comp hf₀
  have hp₁ : IsPGroup 2 f₁.range := hp.of_surjective f₁.rangeRestrict f₁.rangeRestrict_surjective
  obtain ⟨T,hT⟩ := hp₁.exists_le_sylow
  rw [alternatingGroup.two_sylow_eq_kleinFour_of_card_eq_four (by norm_num) T] at hT
  let K := alternatingGroup.kleinFour (Fin 4)
  let : IsKleinFour K := alternatingGroup.kleinFour_isKleinFour (by norm_num)
  let : IsElementaryAbelian 2 K :=
    { toIsMulCommutative := IsKleinFour.isMulCommutative, exponent_dvd_p := by rw [IsKleinFour.exponent_two] }
  let f₂ : D →* K := f₁.codRestrict K (fun x => hT ⟨x,rfl⟩)
  have hf₂ : Function.Injective f₂ := fun _ _ he => hf₁ (congrArg Subtype.val he)
  exact ⟨IsElementaryAbelian.of_injective f₂ hf₂,
    (Nat.card_le_card_of_injective f₂ hf₂).trans_eq (IsKleinFour.card_four)⟩

private theorem seed_pair_transitive_of_generation (h : LocallyRankOneTriple P B)
    {a b : Vertex (family P)} (hab : (graph (family P)).Adj a b)
    (W : Subgroup G) (hgen : W ⊔ Q (family P) a = stabilizer (family P) a)
    {v : Vertex (family P)} (hav : (graph (family P)).Adj a v) :
    ∃ w ∈ W, w • b = v := by
  have hW : W ≤ stabilizer (family P) a := le_sup_left.trans hgen.le
  have hn : W ≤ normalizer (Q (family P) a : Set G) := hW.trans
    ((stabilizer (family P) a).le_normalizer.trans
      (normalizer_le_normalizer_characteristic_image _ (pCore 2 (stabilizer (family P) a))))
  obtain ⟨t,ht,htb⟩ := locally_transitive (family P) hab hav
  have ht' : t ∈ (W : Set G) * (Q (family P) a : Set G) := by
    rw [←coe_mul_of_left_le_normalizer_right W (Q (family P) a) hn,hgen]
    exact ht
  obtain ⟨w,hw,q,hq,rfl⟩ := ht'
  have hqb : q • b = b := ((source_Z_Q_U h a).2.trans
    ((ballKernel_one_le_edge _ hab).trans inf_le_right)) hq
  exact ⟨w,hw,by simpa only [mul_smul,hqb] using htb⟩

/-- The two opposite seeds act transitively on the actual alpha neighbors. -/
theorem source_cubic_a5_opposite_seed_transitive (h : LocallyRankOneTriple P B)
    (hB : ∃ R : Sylow 2 B, (R : Subgroup B) = pCore 2 B)
    (hS : ∀ i, ∃ T : Sylow 2 (P i), (T : Subgroup (P i)).map (P i).subtype ≤ B)
    {a b c : Vertex (family P)} (hc : IsCriticalPair (family P) a b)
    (hb : DGS85.b (family P) = 1)
    (hbc : (graph (family P)).Adj b c) (hac : a ≠ c)
    (hcard : Nat.card ((graph (family P)).neighborSet b) = 3)
    (e : (stabilizer (family P) a ⧸ pCore 2 (stabilizer (family P) a)) ≃*
      alternatingGroup (Fin 5))
    (g : G) (hga : g ∈ stabilizer (family P) a) (hgb : g • b ≠ b)
    {v : Vertex (family P)} (hav : (graph (family P)).Adj a v) :
    ∃ w ∈ (Z (family P) c ⊓ Q (family P) b) ⊔
      (Z (family P) (g • c) ⊓ Q (family P) (g • b)), w • b = v :=
  seed_pair_transitive_of_generation h (source_critical_one_adjacent hc hb) _
    (source_cubic_a5_opposite_seed_generation h hB hS hc hb hbc hac hcard e g hga hgb) hav

/-- The opening faithful-graph vanishing argument in (11.6).
The actual neighboring-core intersection is disjoint from the remote alpha core. -/
theorem source_cubic_a5_neighbor_intersection_separated (h : LocallyRankOneTriple P B)
    (hB : ∃ R : Sylow 2 B, (R : Subgroup B) = pCore 2 B)
    (hS : ∀ i, ∃ T : Sylow 2 (P i), (T : Subgroup (P i)).map (P i).subtype ≤ B)
    {a b c : Vertex (family P)} (hc : IsCriticalPair (family P) a b)
    (hb : DGS85.b (family P) = 1)
    (hbc : (graph (family P)).Adj b c) (hac : a ≠ c)
    (hcard : Nat.card ((graph (family P)).neighborSet b) = 3)
    (e : (stabilizer (family P) a ⧸ pCore 2 (stabilizer (family P) a)) ≃*
      alternatingGroup (Fin 5))
    (g : G) (hga : g ∈ stabilizer (family P) a) (hgb : g • b ≠ b) :
    neighborCoreIntersection (family P) b ⊓ Q (family P) (g • c) = ⊥ := by
  let I := neighborCoreIntersection (family P) b
  let J := I ⊓ Q (family P) (g • c)
  let W := (Z (family P) c ⊓ Q (family P) b) ⊔
    (Z (family P) (g • c) ⊓ Q (family P) (g • b))
  have hab := source_critical_one_adjacent hc hb
  have hW : W ≤ centralizer (J : Set G) := by
    apply sup_le
    · exact inf_le_left.trans ((le_centralizer_iff.mp (source_core_centralizes_center h c)).trans
        (centralizer_le (inf_le_left.trans (neighborCoreIntersection_le _ hbc.symm))))
    · exact inf_le_left.trans
        ((le_centralizer_iff.mp (source_core_centralizes_center h (g • c))).trans
          (centralizer_le inf_le_right))
  have hIa : I ≤ Q (family P) a := neighborCoreIntersection_le _ hab
  have hIE : I ≤ stabilizer (family P) a ⊓ stabilizer (family P) b :=
    hIa.trans ((source_Z_Q_U h a).2.trans (ballKernel_one_le_edge _ hab))
  apply CommutingNontrivial.source_normalized_edge_eq_bot h hab J (inf_le_left.trans hIE)
  · intro v hv
    obtain ⟨w,hw,he⟩ := source_cubic_a5_opposite_seed_transitive h hB hS hc hb hbc hac hcard
      e g hga hgb hv
    exact ⟨w,(hW.trans (Subgroup.centralizer_le_normalizer _)) hw,he⟩
  · intro v hv
    obtain ⟨w,hw,he⟩ := source_neighbor_core_centralizer_transitive h hB hc hb hv
    exact ⟨w,Subgroup.centralizer_le_normalizer _ (centralizer_le (show J ≤ I from inf_le_left) hw.2),he⟩

/-- Separation on every turn `b-a-b'-d`, with no chosen apartment or Cartan. -/
theorem source_cubic_a5_neighbor_intersection_separated_at_turn
    (h : LocallyRankOneTriple P B)
    (hB : ∃ R : Sylow 2 B, (R : Subgroup B) = pCore 2 B)
    (hS : ∀ i, ∃ T : Sylow 2 (P i), (T : Subgroup (P i)).map (P i).subtype ≤ B)
    {a b b' d : Vertex (family P)} (hc : IsCriticalPair (family P) a b)
    (hb : DGS85.b (family P) = 1)
    (hcard : Nat.card ((graph (family P)).neighborSet b) = 3)
    (e : (stabilizer (family P) a ⧸ pCore 2 (stabilizer (family P) a)) ≃*
      alternatingGroup (Fin 5))
    (hab' : (graph (family P)).Adj a b') (hbb' : b ≠ b')
    (hb'd : (graph (family P)).Adj b' d) (had : a ≠ d) :
    neighborCoreIntersection (family P) b ⊓ Q (family P) d = ⊥ := by
  have hab := source_critical_one_adjacent hc hb
  obtain ⟨g,hga,hgb⟩ := locally_transitive (family P) hab hab'
  have hgc : g • (g⁻¹ • d) = d := smul_inv_smul g d
  have hbc : (graph (family P)).Adj b (g⁻¹ • d) := by
    have hh := (Subgroup.CosetGeometry.translationGraphIso (family P) g⁻¹).map_adj_iff.mpr hb'd
    change (graph (family P)).Adj (g⁻¹ • b') (g⁻¹ • d) at hh
    rwa [←hgb,inv_smul_smul] at hh
  have hac : a ≠ g⁻¹ • d := by
    intro he
    apply had
    have hh := congrArg (fun v => g • v) he
    rwa [show g • a = a from hga,hgc] at hh
  have hs := source_cubic_a5_neighbor_intersection_separated h hB hS hc hb hbc hac hcard
    e g hga (by rw [hgb]; exact Ne.symm hbb')
  rwa [hgc] at hs

/-- The subgroup Z₀ in the opening of (11.6) is elementary of order at most four
in the actual cubic A₅ branch. -/
theorem source_cubic_a5_intersection_layer (h : LocallyRankOneTriple P B)
    (hB : ∃ R : Sylow 2 B, (R : Subgroup B) = pCore 2 B)
    (hS : ∀ i, ∃ T : Sylow 2 (P i), (T : Subgroup (P i)).map (P i).subtype ≤ B)
    {a b b' d : Vertex (family P)} (hc : IsCriticalPair (family P) a b)
    (hb : DGS85.b (family P) = 1)
    (hcard : Nat.card ((graph (family P)).neighborSet b) = 3)
    (e : (stabilizer (family P) a ⧸ pCore 2 (stabilizer (family P) a)) ≃*
      alternatingGroup (Fin 5))
    (hab' : (graph (family P)).Adj a b') (hbb' : b ≠ b')
    (hb'd : (graph (family P)).Adj b' d) (had : a ≠ d) :
    IsElementaryAbelian 2 (neighborCoreIntersection (family P) b ⊓ Q (family P) b' : Subgroup G) ∧
      Nat.card (neighborCoreIntersection (family P) b ⊓ Q (family P) b' : Subgroup G) ≤ 4 := by
  let J := neighborCoreIntersection (family P) b ⊓ Q (family P) b'
  let H := stabilizer (family P) d
  have hJH : J ≤ H := inf_le_right.trans ((source_Z_Q_U h b').2.trans
    ((ballKernel_one_le_edge _ hb'd).trans inf_le_right))
  have hsep := source_cubic_a5_neighbor_intersection_separated_at_turn h hB hS hc hb hcard e
    hab' hbb' hb'd had
  obtain ⟨t,_,hta⟩ := locally_transitive (family P) hab'.symm hb'd
  have hs : H = (stabilizer (family P) a).map (MulAut.conj t).toMonoidHom := by
    change stabilizer (family P) d = _
    rw [←hta,stabilizer_translate]
  let es : H ≃* stabilizer (family P) a := (MulEquiv.subgroupCongr hs).trans
    ((stabilizer (family P) a).equivMapOfInjective
      (MulAut.conj t).toMonoidHom (MulAut.conj t).injective).symm
  let ed := (QuotientGroup.congr _ _ es (pCore_map_iso 2 es)).trans e
  let q : H →* alternatingGroup (Fin 5) :=
    ed.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 H))
  let j : J →* H := inclusion hJH
  let f := q.comp j
  have hf : Function.Injective f := by
    apply (MonoidHom.ker_eq_bot_iff f).mp
    apply bot_unique
    intro x hx
    have hxQ : (x : G) ∈ Q (family P) d := by
      have he : ed ((QuotientGroup.mk' (pCore 2 H)) (j x)) = 1 := hx
      rw [map_eq_one_iff ed ed.injective] at he
      have hm := (QuotientGroup.eq_one_iff (j x)).mp he
      exact mem_map_of_mem H.subtype hm
    apply mem_bot.mpr
    apply Subtype.ext
    exact mem_bot.mp (hsep ▸ (show (x : G) ∈ neighborCoreIntersection (family P) b ⊓
      Q (family P) d from ⟨x.property.1,hxQ⟩))
  exact elementary_small_of_a5_embedding ((isPGroup_pCoreIn 2 _).to_le inf_le_right) f hf

end CFSG.Quasithin.ChapterF.Source.DGS85.CommutingOneProfile
