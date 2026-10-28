module
public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.Generation.LinearRecognition.Centralizers.UnitaryExclusion.LocalTwoStructure.SourcePlacement.Actions.RelativeCore
public import Theory.SpecificGroups.SU3.BinaryFixedTorusGeneration

/-!
# Generation of the source root group by the specified fixed torus

Write A=closure(Z∩M), B=d.torus and T=localT Z M u. If B centralized T,
the specified local centralizer equality would place T in L B. The odd
central factor B contributes nothing to a two-subgroup, so T would lie in
the actual PSL₂ subgroup L. Its exponent-two property and the distinguished
involution calculation would give T≤A=Φ(T), contradicting T≠1.

An actual unitary-cover isomorphism and the checked inner normalization of
the Sylow–involution pair put T into the Hermitian root group and B into
the full diagonal torus. The noncentralization just proved supplies a
nonidentity first-coordinate scalar. Its displacement generates every first
coordinate, and squares generate the remaining central coordinates. This
proves the literal ambient equality [B,T]=T in both SU₃ and PSU₃, retaining
the cubic projective kernel and never identifying B by its order alone.

The earlier identification Φ(T)=A remains explicit. Its source producer is
the sibling root-quotient calculation; the source action assembly discharges
that premise. Centralization of A by T is not needed for this equality.

Source: GLS4, Chapter 2, proof of Lemma 13.4, lines 2397–2420 (its torus A
is named B here); Chapter 4, Lemma 3.5(c,d); Huppert II.10.12.
-/

open Subgroup Theory.GroupTheory
namespace BenderSuzuki.ZD.UnitaryExclusion.SourcePlacement
universe v
variable {G : Type v} [Group G] [Finite G]
variable {Z : Set G} {M : Subgroup G} {z t u : G} {n : ℕ}

private theorem twoSubgroup_le_of_central_odd_sup
    (L B T : Subgroup G) (hBL : B ≤ centralizer (L : Set G))
    (hodd : Nat.Coprime 2 (Nat.card B)) (hT : IsPGroup 2 T)
    (hTLB : T ≤ L ⊔ B) : T ≤ L := by
  let K := L ⊔ B
  let L' := L.subgroupOf K
  let B' := B.subgroupOf K
  let T' := T.subgroupOf K
  have hBLn : B ≤ normalizer (L : Set G) := hBL.trans (Subgroup.centralizer_le_normalizer _)
  let : L'.Normal := (normal_subgroupOf_iff_le_normalizer
    (show L ≤ K from le_sup_left)).mpr (sup_le L.le_normalizer hBLn)
  have hsup : L' ⊔ B' = ⊤ := by
    rw [← subgroupOf_sup (show L ≤ K from le_sup_left) (show B ≤ K from le_sup_right)]
    exact subgroupOf_self K
  have hindex : L'.index ∣ Nat.card B' := by
    have hi := L'.relIndex_dvd_card B'
    rwa [← relIndex_sup_left, hsup, relIndex_top_right] at hi
  have hcardB : Nat.card B' = Nat.card B :=
    Nat.card_congr (subgroupOfEquivOfLe (show B ≤ K from le_sup_right)).toEquiv
  have hcop : Nat.Coprime 2 L'.index := hodd.of_dvd_right (hcardB ▸ hindex)
  have hTp : IsPGroup 2 T' := hT.comap_subtype
  obtain ⟨k, hk⟩ := hTp.exists_card_eq
  have hrel : L'.relIndex T' = 1 := Nat.eq_one_of_dvd_coprimes
    (hk ▸ hcop.symm.pow_right k) (L'.relIndex_dvd_index_of_normal T')
    (L'.relIndex_dvd_card T')
  have hle : T' ≤ L' := relIndex_eq_one.mp hrel
  intro x hx
  exact hle (show (⟨x, hTLB hx⟩ : K) ∈ T' from hx)

omit [Finite G] in
private theorem linear_twoSubgroup_exponent
    (e : residualGenerated M z t ≃* MatrixGroups.PSL2BinaryMatrixGroup n)
    (K : Subgroup G) (hK : IsPGroup 2 K) (hKL : K ≤ residualGenerated M z t)
    (x : K) : x ^ 2 = 1 := by
  let q : Converse.SL2 (PFAppendixIII.BinaryGaloisField n) ≃*
      MatrixGroups.PSL2MatrixGroup (PFAppendixIII.BinaryGaloisField n) :=
    MulEquiv.ofBijective (Converse.pi _) ⟨Converse.pi_injective, Converse.pi_surjective⟩
  let f : K →* Converse.SL2 (PFAppendixIII.BinaryGaloisField n) :=
    q.symm.toMonoidHom.comp (e.toMonoidHom.comp (Subgroup.inclusion hKL))
  have hf : Function.Injective f :=
    q.symm.injective.comp (e.injective.comp (Subgroup.inclusion_injective hKL))
  have hp : IsPGroup 2 f.range :=
    hK.of_surjective f.rangeRestrict f.rangeRestrict_surjective
  have hs := Matrix.SpecialLinearGroup.twoSubgroup_pow_two f.range hp (f.rangeRestrict x)
  apply hf
  rw [map_pow, map_one]
  exact congrArg Subtype.val hs

private theorem torus_not_centralizes_localT
    (h : MinimalCounterexample Z M) (r : SimpleReduction Z M)
    (ha : ResidualAction Z M) (hz : z ∈ Z) (hzM : z ∈ M)
    (ht : t ∈ Z) (htM : t ∉ M) (hL : residualGenerated M z t ≠ ⊤)
    (heven : Even (Nat.card (residualPairStabilizer M t)))
    (hn : 2 ≤ n)
    (huD : u ∈ residualPairStabilizer M t) (hu : PFAppendixIII.IsInvolution u)
    (d : SecondCentralizerData Z M z t u n)
    (e : residualGenerated M z t ≃* MatrixGroups.PSL2BinaryMatrixGroup n)
    (hPhi : (frattini (localT Z M u)).map (localT Z M u).subtype =
      closure (Z ∩ (M : Set G))) :
    ¬ d.torus ≤ centralizer (localT Z M u : Set G) := by
  intro hc
  obtain ⟨hAL, hMA, hA, hZ⟩ := distinguishedClosure_data h r ha hz hzM ht htM hL heven
  have hTp : IsPGroup 2 (localT Z M u) := isPGroup_pCoreIn 2 _
  have hTLB : localT Z M u ≤ residualGenerated M z t ⊔ d.torus := by
    rw [← d.local_torus_centralizer]
    exact le_inf ((localTwoCore_le _ _).trans inf_le_right) (le_centralizer_iff.mp hc)
  have hTL := twoSubgroup_le_of_central_odd_sup _ _ _ d.torus_centralizes
    (torus_coprime (by omega) d) hTp hTLB
  have hTA : localT Z M u ≤ closure (Z ∩ (M : Set G)) := by
    intro x hx
    exact (localT_involutions h.disconnected r htM huD hu hZ ⟨x, hx⟩).mpr
      (linear_twoSubgroup_exponent e _ hTp hTL ⟨x, hx⟩)
  have hPhiTop : frattini (localT Z M u) = ⊤ := by
    apply top_unique
    intro x _
    have hx : (x : G) ∈ (frattini (localT Z M u)).map (localT Z M u).subtype :=
      hPhi ▸ hTA x.property
    obtain ⟨y, hy, he⟩ := hx
    exact (Subtype.ext he : y = x) ▸ hy
  have hbot : (⊥ : Subgroup (localT Z M u)) = ⊤ :=
    frattini_nongenerating (by rw [hPhiTop]; exact sup_eq_right.mpr bot_le)
  apply localT_ne_bot h.disconnected hz hzM hAL hMA hA d
  apply eq_bot_iff.mpr
  intro x hx
  have he : (⟨x, hx⟩ : localT Z M u) = 1 :=
    mem_bot.mp (hbot ▸ mem_top _)
  exact congrArg Subtype.val he
end BenderSuzuki.ZD.UnitaryExclusion.SourcePlacement

noncomputable section
namespace BenderSuzuki.ZD.UnitaryExclusion.SourcePlacement
open Subgroup Theory.GroupTheory PFchapter1section1 PFAppendixIII RankOneModelGeometry
open _root_.BenderSuzuki.MatrixGroups _root_.BenderSuzuki.MatrixGroups.HermitianForm

private theorem twoPoint_map_equiv {H K : Type*} [Group H] [Group K]
    (e : H ≃* K) (B : Subgroup H) (t : H) :
    (twoPoint B t).map e.toMonoidHom = twoPoint (B.map e.toMonoidHom) (e t) := by
  rw [twoPoint, twoPoint, Subgroup.map_inf _ _ _ e.injective]
  congr 1
  simp only [rightConjugate, Subgroup.conjBy, Subgroup.map_map]
  congr 1
  ext x
  simp

private theorem noncentral_map {H K : Type*} [Group H] [Group K]
    (f : H →* K) (hf : Function.Injective f) (B T : Subgroup H)
    (hne : ¬ B ≤ centralizer (T : Set H)) :
    ¬ B.map f ≤ centralizer (T.map f : Set K) := by
  intro hc
  apply hne
  intro b hb x hx
  apply hf
  simpa only [map_mul] using hc (mem_map_of_mem f hb) (f x) (mem_map_of_mem f hx)

private theorem generation_of_normalized_model
    {H K : Type*} [Group H] [Group K]
    (e : H ≃* K) (P : Subgroup H) (B D : Subgroup H)
    (R S : Subgroup K) (hP : P.map e.toMonoidHom = R)
    (hD : D.map e.toMonoidHom = S) (hB : B ≤ D)
    (hne : ¬ B ≤ centralizer (P : Set H))
    (hmodel : ∀ C : Subgroup K, C ≤ S →
      (¬ C ≤ centralizer (R : Set K)) → ⁅C, R⁆ = R) : ⁅B, P⁆ = P := by
  apply map_injective (f := e.toMonoidHom) e.injective
  rw [map_commutator, hP]
  apply hmodel
  · rw [← hD]
    exact map_mono hB
  · rw [← hP]
    exact noncentral_map e.toMonoidHom e.injective B P hne

private theorem cover_commutator_eq
    {H : Type*} [Group H] [Finite H] {n : ℕ}
    (hn : 2 ≤ n) (hc : IsUnitaryCentralizerCoverAt n H)
    (P : Sylow 2 H) (t : H) (ht : PFAppendixIII.IsInvolution t)
    (htN : t ∉ normalizer (P : Set H))
    (B : Subgroup H) (hB : B ≤ twoPoint (normalizer (P : Set H)) t)
    (hne : ¬ B ≤ centralizer (P : Set H)) : ⁅B, (P : Subgroup H)⁆ = P := by
  obtain ⟨E, _, _, J, hJ, hcard, hfixed, he | he⟩ := hc
  · obtain ⟨e⟩ := he
    let : Finite (ProjectiveSpecialUnitaryMatrixGroup J) := Finite.of_equiv H e.toEquiv
    let : Fintype E := Fintype.ofFinite E
    let : CharP E 2 := charP_of_card_eq_prime_pow (p := 2) (f := n * 2)
      (by simpa only [Nat.card_eq_fintype_card, pow_mul] using hcard)
    let Q := P.mapSurjective (f := e.toMonoidHom) e.surjective
    have hN : (normalizer (P : Set H)).map e.toMonoidHom = normalizer (Q : Set _) :=
      map_equiv_normalizer_eq (P : Subgroup H) e
    have htQ : e t ∉ normalizer (Q : Set _) := by
      rw [← hN]
      intro hh
      obtain ⟨x, hx, he⟩ := hh
      exact htN (e.injective he ▸ hx)
    obtain ⟨g, hQg, _, hDg⟩ := PairNormalization.projective_pair J hJ hn hcard hfixed Q
      (e t) (⟨fun he => ht.1 (e.injective (he.trans (map_one e).symm)),
        by rw [← map_pow, ht.2, map_one]⟩) htQ
    let c := e.trans (MulAut.conj g)
    have hP : (P : Subgroup H).map c.toMonoidHom = BorelTorus.projectiveRoot J hJ := by
      change (P : Subgroup H).map ((MulAut.conj g).toMonoidHom.comp e.toMonoidHom) = _
      rw [← map_map]
      exact hQg
    have hD : (twoPoint (normalizer (P : Set H)) t).map c.toMonoidHom =
        BorelTorus.projectiveTorus J hJ := by
      change (twoPoint (normalizer (P : Set H)) t).map
        ((MulAut.conj g).toMonoidHom.comp e.toMonoidHom) = _
      rw [← map_map, twoPoint_map_equiv, hN]
      exact hDg
    exact generation_of_normalized_model c P B _ _ _ hP hD hB hne
      (BinaryFixedTorusGeneration.projective_commutator_eq J hcard hfixed hJ)
  · obtain ⟨e⟩ := he
    let : Fintype E := Fintype.ofFinite E
    let : CharP E 2 := charP_of_card_eq_prime_pow (p := 2) (f := n * 2)
      (by simpa only [Nat.card_eq_fintype_card, pow_mul] using hcard)
    let Q := P.mapSurjective (f := e.toMonoidHom) e.surjective
    have hN : (normalizer (P : Set H)).map e.toMonoidHom = normalizer (Q : Set _) :=
      map_equiv_normalizer_eq (P : Subgroup H) e
    have htQ : e t ∉ normalizer (Q : Set _) := by
      rw [← hN]
      intro hh
      obtain ⟨x, hx, he⟩ := hh
      exact htN (e.injective he ▸ hx)
    obtain ⟨g, hQg, _, hDg⟩ := PairNormalization.special_pair J hJ hn hcard hfixed Q
      (e t) (⟨fun he => ht.1 (e.injective (he.trans (map_one e).symm)),
        by rw [← map_pow, ht.2, map_one]⟩) htQ
    let c := e.trans (MulAut.conj g)
    have hP : (P : Subgroup H).map c.toMonoidHom = BorelTorus.specialRoot J hJ := by
      change (P : Subgroup H).map ((MulAut.conj g).toMonoidHom.comp e.toMonoidHom) = _
      rw [← map_map]
      exact hQg
    have hD : (twoPoint (normalizer (P : Set H)) t).map c.toMonoidHom =
        BorelTorus.specialTorus J hJ := by
      change (twoPoint (normalizer (P : Set H)) t).map
        ((MulAut.conj g).toMonoidHom.comp e.toMonoidHom) = _
      rw [← map_map, twoPoint_map_equiv, hN]
      exact hDg
    exact generation_of_normalized_model c P B _ _ _ hP hD hB hne
      (BinaryFixedTorusGeneration.special_commutator_eq J hcard hfixed hJ)
end BenderSuzuki.ZD.UnitaryExclusion.SourcePlacement
namespace BenderSuzuki.ZD.UnitaryExclusion.SourcePlacement
open Subgroup Theory.GroupTheory PFchapter1section1 PFAppendixIII RankOneModelGeometry
/-- The literal source equality T=[B,T] for the specified second-centralizer
torus. Only the earlier Frattini identification is needed; centralization
of A by T is unnecessary for this particular conclusion. -/
public theorem source_fixedTorus_commutator_eq
    {G : Type*} [Group G] [Finite G]
    {Z : Set G} {M : Subgroup G} {z t u : G} {n : ℕ}
    (h : MinimalCounterexample Z M) (r : SimpleReduction Z M)
    (ha : ResidualAction Z M) (hz : z ∈ Z) (hzM : z ∈ M)
    (ht : t ∈ Z) (htM : t ∉ M) (hL : residualGenerated M z t ≠ ⊤)
    (heven : Even (Nat.card (residualPairStabilizer M t)))
    (hn : 2 ≤ n) (hunitary : ResidualUnitaryCentralizers Z M z t n)
    (huD : u ∈ residualPairStabilizer M t) (hu : PFAppendixIII.IsInvolution u)
    (d : SecondCentralizerData Z M z t u n)
    (e : residualGenerated M z t ≃* MatrixGroups.PSL2BinaryMatrixGroup n)
    (hPhi : (frattini (localT Z M u)).map (localT Z M u).subtype =
      closure (Z ∩ (M : Set G))) :
    ⁅d.torus, localT Z M u⁆ = localT Z M u := by
  let H := centralizerClosure Z u
  obtain ⟨_, P, hP⟩ := pair_involution_unitary_borel h.disconnected r htM huD hu hn
    (hunitary u huD hu).2
  change M.comap H.subtype = normalizer (P : Set H) at hP
  have hPT : (P : Subgroup H).map H.subtype = localT Z M u := by
    apply sylow_map_eq_pCoreIn_of_normalizer_map_eq P H.subtype H.subtype_injective
      (M ⊓ H)
    change (normalizer (P : Set H)).map H.subtype = _
    rw [← hP, map_comap_eq, range_subtype, inf_comm]
  have htH : t ∈ H := (hunitary u huD hu).1.le
    ((show zpowers t ≤ residualGenerated M z t from le_sup_right.trans le_sup_left)
      (mem_zpowers t))
  let B := d.torus.subgroupOf H
  have hBmap : B.map H.subtype = d.torus := map_subgroupOf_eq_of_le d.torus_le_local
  have hBD : B ≤ twoPoint (normalizer (P : Set H)) (⟨t, htH⟩ : H) := by
    rw [← hP]
    apply (map_le_map_iff_of_injective H.subtype_injective).mp
    rw [hBmap, ← localPair_eq_map htH]
    exact le_inf d.torus_le_pair d.torus_le_local
  have hne : ¬ B ≤ centralizer (P : Set H) := by
    intro hc
    apply torus_not_centralizes_localT h r ha hz hzM ht htM hL heven hn huD hu d e hPhi
    intro b hb x hx
    obtain ⟨b₀, hb₀, rfl⟩ := (show b ∈ B.map H.subtype from hBmap ▸ hb)
    obtain ⟨x₀, hx₀, rfl⟩ := (show x ∈ (P : Subgroup H).map H.subtype from hPT ▸ hx)
    exact congrArg Subtype.val (hc hb₀ x₀ hx₀)
  have hgen := cover_commutator_eq hn (hunitary u huD hu).2 P ⟨t, htH⟩
    (⟨fun he => (h.disconnected.involutions t ht).1 (congrArg Subtype.val he),
      Subtype.ext (h.disconnected.involutions t ht).2⟩)
    (by rw [← hP]; exact htM) B hBD hne
  have hm := congrArg (fun K : Subgroup H => K.map H.subtype) hgen
  simpa only [map_commutator, hBmap, hPT] using hm

end BenderSuzuki.ZD.UnitaryExclusion.SourcePlacement
