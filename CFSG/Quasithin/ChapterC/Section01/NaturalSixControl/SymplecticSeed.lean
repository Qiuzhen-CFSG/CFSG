module
public import CFSG.Quasithin.ChapterC.Section01.NaturalSixControl.SymplecticSetup.Source
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Setup.Critical

/-!
# Natural six-module control of the MS93 seed layer

The marked nonzero vector in the actual natural module is fixed by the edge
radical. Its omega-one center therefore lies in the ambient two-core because
the natural action has centralizer exactly that two-core. Conjugation in the
free holomorph graph identifies the base Z-layer with the normal closure of
this seed. The alternating component action then spans the whole natural
module inside the Z-layer, preserving the literal S6 quotient and coordinates.
Consequently critical distance zero is impossible in the actual source.

These are source-side module and seed facts only; no MS93 classification or
whole-core conclusion is asserted.
-/


@[expose] public section
namespace CFSG.Quasithin.ChapterC.NaturalSixControl.SymplecticSeed
open Subgroup Theory.GroupTheory
open BinaryMS.MS93 Stellmacher.PushingUp.AmalgamGraph
universe u
variable {M : Type u} [Group M] [Finite M]

/-- The first omega layer at the base holomorph vertex lies in the base Z-layer. -/
theorem seed_le_Z (R : Subgroup M) :
    (omegaCenter R).map (embedM R) ≤ Z R (alpha R) := by
  have hb : edgeOmega R (beta R) ≤ Z R (alpha R) := by
    rw [Z, if_pos (show color R (alpha R) = false from rfl)]
    exact le_iSup_of_le (beta R) (le_iSup_of_le (base_adjacent R) le_rfl)
  rwa [edgeOmega, Q_beta, omegaCenter_map R (embedM R) (embedM_injective R)] at hb

/-- Every neighbor omega layer is an original-group conjugate of the seed. -/
theorem Z_le_map_of_seed_le (R N : Subgroup M) [N.Normal]
    (hs : omegaCenter R ≤ N) : Z R (alpha R) ≤ N.map (embedM R) := by
  rw [Z, if_pos (show color R (alpha R) = false from rfl)]
  apply iSup_le
  intro b
  apply iSup_le
  intro hb
  obtain ⟨g, hg, hgb⟩ := stabilizer_transitive_neighbors R (alpha R) (base_adjacent R) hb
  rw [← hgb, edgeOmega_act]
  change (omegaCenter (Q R (beta R))).map (MulAut.conj g⁻¹).toMonoidHom ≤ _
  rw [Q_beta, omegaCenter_map R (embedM R) (embedM_injective R)]
  rintro x ⟨y, ⟨r, hr, rfl⟩, rfl⟩
  change g ∈ stabilizer R (mVertex R 1) at hg
  rw [stabilizer_m_base] at hg
  obtain ⟨m, rfl⟩ := hg
  refine ⟨m⁻¹ * r * m, ?_, ?_⟩
  · change m⁻¹ * r * m ∈ N
    have hn := (inferInstance : N.Normal).conj_mem r (hs hr) m⁻¹
    rwa [inv_inv] at hn
  · change embedM R (m⁻¹ * r * m) =
      (embedM R m)⁻¹ * embedM R r * ((embedM R m)⁻¹)⁻¹
    rw [map_mul, map_mul, map_inv, inv_inv]

omit [Finite M] in
theorem Z_comap_normal (R : Subgroup M) :
    ((Z R (alpha R)).comap (embedM R)).Normal := by
  refine ⟨?_⟩
  intro x hx g
  change embedM R (g * x * g⁻¹) ∈ Z R (alpha R)
  rw [map_mul, map_mul, map_inv]
  have hg : embedM R g ∈ stabilizer R (alpha R) := by
    rw [show alpha R = mVertex R 1 from rfl, stabilizer_m_base]
    exact ⟨g, rfl⟩
  exact le_normalizer_iff.mp (Z_normalized R (alpha R)) _ hg _ hx

/-- The graph Z-layer is exactly the normal closure of the original omega seed. -/
theorem Z_eq_seedHull (R : Subgroup M) :
    Z R (alpha R) = (normalClosure (omegaCenter R : Set M)).map (embedM R) := by
  apply le_antisymm
  · exact Z_le_map_of_seed_le R _ subset_normalClosure
  · apply map_le_iff_le_comap.mpr
    let := Z_comap_normal R
    apply normalClosure_le_normal
    exact map_le_iff_le_comap.mp (seed_le_Z R)

omit [Finite M] in
/-- Centralizing the original natural subgroup forces the edge omega seed
into the original two-core. -/
theorem seed_le_core {R W : Subgroup M} (hWR : W ≤ R)
    (hCW : centralizer (W : Set M) = pCore 2 M) :
    omegaCenter R ≤ pCore 2 M := by
  rw [← hCW]
  intro x hx y hy
  exact (mem_omegaCenter_iff.mp hx).2.2 y (hWR hy)

/-- The actual natural subgroup eliminates critical distance zero directly. -/
theorem criticalDistance_pos {R W : Subgroup M} (hp : IsPGroup 2 R)
    (hQ : pCore 2 M ≤ R) (hWR : W ≤ R)
    (hCW : centralizer (W : Set M) = pCore 2 M)
    (he : ∃ n, CriticalRadius R (alpha R) n) :
    0 < criticalDistance R (alpha R) he := by
  have hZ : Z R (alpha R) ≤ Q R (alpha R) := by
    rw [Q_alpha R hp hQ]
    exact Z_le_map_of_seed_le R _ (seed_le_core hWR hCW)
  obtain ⟨a, hc⟩ := criticalPair_exists R (alpha R) he
  by_contra! hz
  have hd : (cosetGraph R).dist (alpha R) a = 0 := by
    rw [hc.1]
    omega
  have heq : alpha R = a := (cosetGraph_connected R).dist_eq_zero_iff.mp hd
  exact hc.2 (heq ▸ hZ)


omit [Finite M] in
/-- A marked fixed vector in the original natural module generates that whole
module inside the omega-seed hull. The quotient map and action remain literal. -/
theorem module_le_seedHull {L R W : Subgroup M} [W.Normal]
    (q : M →* Equiv.Perm (Fin 6))
    (hL : L.map q = alternatingGroup (Fin 6))
    (e : W ≃* Multiplicative (BinaryPermutation.natural (Fin 6)))
    (hact : ∀ g w, (e (MulAut.conjNormal g w)).toAdd =
      BinaryPermutation.naturalRepresentation (Fin 6) (q g) (e w).toAdd)
    (hW : IsElementaryAbelian 2 W) (hWR : W ≤ R)
    (w : W) (hw : w ≠ 1) (hfix : ∀ r ∈ R, r * (w : M) = w * r) :
    W ≤ normalClosure (omegaCenter R : Set M) := by
  let := hW
  have hs : (w : M) ∈ omegaCenter R := mem_omegaCenter_iff.mpr
    ⟨hWR w.property, elemPow_eq_one_of_isElementaryAbelian _ w.property, hfix⟩
  have hw0 : (e w).toAdd ≠ 0 := by
    intro h
    apply hw
    apply e.injective
    apply Multiplicative.toAdd.injective
    rw [map_one]
    exact h
  intro x hx
  by_cases hx1 : x = 1
  · rw [hx1]
    exact one_mem _
  let xW : W := ⟨x, hx⟩
  have hx0 : (e xW).toAdd ≠ 0 := by
    intro h
    apply hx1
    have he : xW = 1 := e.injective (by
      apply Multiplicative.toAdd.injective
      rw [map_one]
      exact h)
    exact congrArg Subtype.val he
  obtain ⟨a, ha⟩ := Theory.SpecificGroups.SymmetricSix.BinaryFlags.NaturalTransport.transitive_nonzero
    (e w).toAdd (e xW).toAdd hw0 hx0
  obtain ⟨l, hl, hql⟩ := hL.ge a.property
  have hc : l * (w : M) * l⁻¹ = x := by
    have he : MulAut.conjNormal l w = xW := by
      apply e.injective
      apply Multiplicative.toAdd.injective
      rw [hact, hql]
      exact ha
    exact congrArg Subtype.val he
  rw [← hc]
  exact (inferInstance : (normalClosure (omegaCenter R : Set M)).Normal).conj_mem
    _ (subset_normalClosure hs) l

/-- The same inclusion in the actual free holomorph amalgam. -/
theorem module_le_Z {L R W : Subgroup M} [W.Normal]
    (q : M →* Equiv.Perm (Fin 6))
    (hL : L.map q = alternatingGroup (Fin 6))
    (e : W ≃* Multiplicative (BinaryPermutation.natural (Fin 6)))
    (hact : ∀ g w, (e (MulAut.conjNormal g w)).toAdd =
      BinaryPermutation.naturalRepresentation (Fin 6) (q g) (e w).toAdd)
    (hW : IsElementaryAbelian 2 W) (hWR : W ≤ R)
    (w : W) (hw : w ≠ 1) (hfix : ∀ r ∈ R, r * (w : M) = w * r) :
    W.map (embedM R) ≤ Z R (alpha R) := by
  rw [Z_eq_seedHull]
  exact map_mono (module_le_seedHull q hL e hact hW hWR w hw hfix)

end CFSG.Quasithin.ChapterC.NaturalSixControl.SymplecticSeed
