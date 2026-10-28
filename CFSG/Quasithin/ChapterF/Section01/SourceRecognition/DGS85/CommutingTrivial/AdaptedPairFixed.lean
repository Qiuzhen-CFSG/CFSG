module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingTrivial.AdaptedPairNatural
public import Theory.Representation.BinaryConjugationSection.SL2OddCentralizers

/-!
# The fixed subgroup of the middle core

The neighboring derived-core bound propagates through the full Sylow-image
normal closure to every odd actor in L_x. Coprime decomposition then gives
Q_beta ∩ Q_d = C_(Q_x)(T) Z_x. The natural sections of Z_x and M/Z_x imply
that T fixes no nonidentity element of M. All actions retain their literal
conjugation coordinates.

Source: DGS, *Groups and Graphs* (1985), printed p.150, the definition of R
and the final fixed-point argument.
-/

public noncomputable section
open Subgroup Representation
open Subgroup.CosetGeometry.RankTwo Theory.GroupTheory.AmalgamGraph
open scoped MatrixGroups IsMulCommutative
namespace CFSG.Quasithin.ChapterF.Source.DGS85.CommutingTrivial
variable {G : Type*} [Group G] {P : Fin 2 → Subgroup G} {B : Subgroup G}
private theorem adapted_residual_le_actor_span
    (h : LocallyRankOneTriple P B) (v : Vertex (family P))
    {F : Type*} [Field F] [Finite F] [CharP F 2]
    (e : (graphLocalGroup (family P) v ⧸ pCore 2 (graphLocalGroup (family P) v)) ≃* SL(2,F))
    (A : Subgroup G) (hp : IsPGroup 2 A) (hA : A ≤ graphLocalGroup (family P) v)
    (hi : (Q (family P) v).relIndex A = Nat.card F) :
    (pResidual 2 (graphLocalGroup (family P) v)).map (graphLocalGroup (family P) v).subtype ≤
      conjugateSpanBy A (graphLocalGroup (family P) v) := by
  let := finite_endpoints h
  let H := graphLocalGroup (family P) v
  let : Finite H := Finite.of_injective (inclusion (sylowGenerated_le _)) (inclusion_injective _)
  let q := e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 H))
  have hq : Function.Surjective q := e.surjective.comp (QuotientGroup.mk'_surjective _)
  have hk : q.ker = pCore 2 H := by
    rw [MonoidHom.ker_comp_of_injective _ _ e.injective,QuotientGroup.ker_mk']
  let I := (A.subgroupOf H).map q
  obtain ⟨T,hT⟩ := (hp.comap_subtype.map q).exists_le_sylow
  have hkmap : q.ker.map H.subtype = Q (family P) v := hk ▸ graphLocalGroup_core h v
  have hcard : Nat.card I = Nat.card F := by
    rw [←relIndex_ker,←relIndex_map_map_of_injective _ _ H.subtype_injective,
      hkmap,map_subgroupOf_eq_of_le hA,hi]
  have hTI : I = T := eq_of_le_of_card_ge hT (by
    rw [hcard]
    exact (Nat.card_congr (Matrix.SpecialLinearGroup.sylowEquivAdditive F 2 T).toEquiv).ge)
  let X := normalClosure (A.subgroupOf H : Set H)
  let : (X.map q).Normal := (inferInstance : X.Normal).map q hq
  have hTX : (T : Subgroup SL(2,F)) ≤ X.map q := hTI ▸ map_mono
    (show A.subgroupOf H ≤ X from le_normalClosure)
  obtain ⟨g,_,hg⟩ := Matrix.SpecialLinearGroup.exists_residual_conjugate_sylow_image_sup_eq_top
    T (MonoidHom.id SL(2,F)) Function.surjective_id
  simp only [Subgroup.map_id] at hg
  have hmap : X.map q = ⊤ := by
    apply top_unique
    rw [←hg]
    refine sup_le hTX ?_
    rintro _ ⟨x,hx,rfl⟩
    exact (inferInstance : (X.map q).Normal).conj_mem x (hTX hx) g
  have hsup : X ⊔ q.ker = ⊤ := by
    simpa only [comap_map_eq,comap_top] using congrArg (Subgroup.comap q) hmap
  have hr : pResidual 2 H ≤ X :=
    sInf_le ⟨inferInstance,isPGroup_quotient_of_sup_eq_top X q.ker (hk ▸ pCore_isPGroup) hsup⟩
  have hm := map_mono (f := H.subtype) hr
  rw [map_normalClosure_eq_conjugateSpanBy_range,range_subtype,
    map_subgroupOf_eq_of_le hA] at hm
  exact hm

private theorem adapted_coprime_decomposition (N T : Subgroup G) [Finite N] [Finite T]
    (hn : T ≤ normalizer (N : Set G)) (hs : Group.IsSolvable N)
    (hc : Nat.Coprime (Nat.card T) (Nat.card N)) :
    N = ⁅N,T⁆ ⊔ (N ⊓ centralizer (T : Set G)) := by
  let : Normalizes T N := ⟨hn⟩
  have he := fixedPointSubgroup_sup_commutatorAction_eq_top_of_solvable_coprime
    (G := N) (A := T) hs hc
  have hm := congrArg (fun U : Subgroup N => U.map N.subtype) he
  rw [Subgroup.map_sup,commutatorAction_subgroup_conj_map_eq_commutator N T hn,
    fixedPointSubgroup_subgroup_conj_eq_subgroupCentralizerIn N T hn,
    map_subgroupOf_eq_of_le (show subgroupCentralizerIn N T ≤ N from inf_le_left),
    ←MonoidHom.range_eq_map,range_subtype,sup_comm] at hm
  exact hm.symm


/-- Odd actors in the middle local group act trivially on the neighboring
core intersection modulo its original center. -/
theorem adjacent_core_odd_commutator
    (h : LocallyRankOneTriple P B)
    (hB : ∃ T : Sylow 2 B, (T : Subgroup B) = pCore 2 B)
    (hS : ∀ i, ∃ T : Sylow 2 (P i), (T : Subgroup (P i)).map (P i).subtype ≤ B)
    {beta x d : Vertex (family P)}
    (hd : (graph (family P)).Adj x d) (he : ¬ Q (family P) d ≤ Q (family P) x)
    {F : Type*} [Field F] [Finite F] [CharP F 2]
    (ex : (graphLocalGroup (family P) x ⧸ pCore 2 (graphLocalGroup (family P) x)) ≃* SL(2,F))
    (hN : graphLocalGroup (family P) x ≤ normalizer
      ((Q (family P) beta ⊓ Q (family P) d : Subgroup G) : Set G))
    (hdd : ⁅Q (family P) d,Q (family P) d⁆ ≤ Z (family P) d)
    (hZd : Z (family P) d ≤ Z (family P) x)
    (T : Subgroup G) (hT : T ≤ graphLocalGroup (family P) x) (ho : Odd (Nat.card T)) :
    ⁅Q (family P) beta ⊓ Q (family P) d,T⁆ ≤ Z (family P) x := by
  let := finite_endpoints h
  let Γ := family P
  let H := graphLocalGroup Γ x
  have hTR : T ≤ (pResidual 2 H).map H.subtype := by
    intro t ht
    refine ⟨⟨t,hT ht⟩,?_,rfl⟩
    apply mem_pResidual_of_orderOf_coprime
    rw [Subgroup.orderOf_mk]
    exact ho.coprime_two_left.of_dvd_right (T.orderOf_dvd_natCard ht)
  have hA := neighbor_core_le_localGroup h hB hS hd
  have hgen := adapted_residual_le_actor_span h x ex (Q Γ d)
    (isPGroup_pCoreIn 2 _) hA (linear_adjacent_core_index h hB hS hd he ex)
  rw [commutator_comm]
  apply (commutator_mono (hTR.trans hgen) le_rfl).trans
  rw [commutator_conjugateSpanBy_of_normalized_right _ _ _ hA hN]
  exact conjugateSpanBy_le (((commutator_mono le_rfl inf_le_right).trans hdd).trans hZd)
    ((sylowGenerated_le _).trans (CommutingNontrivial.stabilizer_normalizes_Z Γ x))

/-- The odd fixed subgroup supplements Z_x in the original neighboring
core intersection, and the constructed natural M has no odd fixed points. -/
theorem adjacent_core_odd_fixed_decomposition
    (h : LocallyRankOneTriple P B)
    {beta x d : Vertex (family P)}
    {F : Type*} [Field F] [Finite F] [CharP F 2]
    (ex : (graphLocalGroup (family P) x ⧸ pCore 2 (graphLocalGroup (family P) x)) ≃* SL(2,F))
    {n : ℕ} (hn : 1 < n) (hF : Nat.card F = 2^n)
    (hsec : CoreQuotientSection (family P) beta x d F ex)
    (hNQ : Q (family P) beta ⊓ Q (family P) d ≤ Q (family P) x)
    (hNN : graphLocalGroup (family P) x ≤ normalizer
      ((Q (family P) beta ⊓ Q (family P) d : Subgroup G) : Set G))
    (hZN : Z (family P) x ≤ Q (family P) beta ⊓ Q (family P) d)
    (M T : Subgroup G)
    (hT : T ≤ graphLocalGroup (family P) x) (ho : Odd (Nat.card T)) (hne : T ≠ ⊥)
    (hcomm : ⁅Q (family P) beta ⊓ Q (family P) d,T⁆ ≤ Z (family P) x)
    (cZ : letI : Algebra (ZMod 2) F := ZMod.algebra F 2
      BinaryConjugationSection (graphLocalGroup (family P) x) (Z (family P) x) ⊥
        (((specialLinearNatural (k := F) 2).restrictScalars (k := ZMod 2)).comp
          (ex.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 (graphLocalGroup (family P) x))))))
    (cM : letI : Algebra (ZMod 2) F := ZMod.algebra F 2
      BinaryConjugationSection (graphLocalGroup (family P) x) M (Z (family P) x)
        (((specialLinearNatural (k := F) 2).restrictScalars (k := ZMod 2)).comp
          (ex.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 (graphLocalGroup (family P) x)))))) :
    let R := Q (family P) x ⊓ centralizer (T : Set G)
    R ≤ Q (family P) beta ⊓ Q (family P) d ∧
      Q (family P) beta ⊓ Q (family P) d = R ⊔ Z (family P) x ∧
      M ⊓ centralizer (T : Set G) = ⊥ := by
  let : Algebra (ZMod 2) F := ZMod.algebra F 2
  let := finite_endpoints h
  let Γ := family P
  let H := graphLocalGroup Γ x
  let N := Q Γ beta ⊓ Q Γ d
  let R := Q Γ x ⊓ centralizer (T : Set G)
  let : Finite N := Finite.of_injective (inclusion (hNQ.trans (Q_le_stabilizer Γ x)))
    (inclusion_injective _)
  let : Finite T := Finite.of_injective (inclusion (hT.trans (sylowGenerated_le _)))
    (inclusion_injective _)
  let π := ex.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 H))
  have hp : IsPGroup 2 π.ker := by
    have he : π.ker = pCore 2 H := by
      rw [MonoidHom.ker_comp_of_injective _ _ ex.injective,QuotientGroup.ker_mk']
    rw [he]
    exact pCore_isPGroup
  obtain ⟨hN,_,hE,σ,c,_,he⟩ := hsec
  let := hN
  let := hE
  obtain ⟨E,hE⟩ := he n hn hF
  have hRN : R ≤ N := BinaryConjugationSection.natural_odd_centralizer_le_kernel
    H (Q Γ x) N π hp σ c E hE T hT ho hne
  have hpN : IsPGroup 2 N := (isPGroup_pCoreIn 2 _).to_le hNQ
  have hcop : Nat.Coprime (Nat.card T) (Nat.card N) := by
    obtain ⟨k,hk⟩ := hpN.exists_card_eq
    rw [hk]
    exact ho.coprime_two_right.pow_right k
  have hdec := adapted_coprime_decomposition N T (hT.trans hNN)
    (@IsNilpotent.to_isSolvable N _ hpN.isNilpotent) hcop
  have hRC : N ⊓ centralizer (T : Set G) = R :=
    le_antisymm (inf_le_inf_right _ hNQ) (le_inf hRN inf_le_right)
  have hNR : N = R ⊔ Z Γ x := le_antisymm
    (hdec.le.trans (sup_le (hcomm.trans le_sup_right) (hRC.le.trans le_sup_left)))
    (sup_le hRN hZN)
  have hCZ : Z Γ x ⊓ centralizer (T : Set G) ≤ (⊥ : Subgroup G) :=
    BinaryConjugationSection.natural_odd_centralizer_le_kernel H (Z Γ x) ⊥ π hp
      ((specialLinearNatural (k := F) 2).restrictScalars (k := ZMod 2)) cZ
      (LinearEquiv.refl _ _) (fun _ _ => rfl) T hT ho hne
  have hCM : M ⊓ centralizer (T : Set G) ≤ Z Γ x :=
    BinaryConjugationSection.natural_odd_centralizer_le_kernel H M (Z Γ x) π hp
      ((specialLinearNatural (k := F) 2).restrictScalars (k := ZMod 2)) cM
      (LinearEquiv.refl _ _) (fun _ _ => rfl) T hT ho hne
  exact ⟨hRN,hNR,bot_unique ((le_inf hCM inf_le_right).trans hCZ)⟩


/-- The native center action gives the literal zero-kernel natural section. -/
theorem graph_natural_center_section
    (h : LocallyRankOneTriple P B) (x : Vertex (family P))
    {F : Type*} [Field F] [Finite F] [CharP F 2]
    (ex : (graphLocalGroup (family P) x ⧸ pCore 2 (graphLocalGroup (family P) x)) ≃* SL(2,F)) :
    letI := Z_elementary (family P) (fun v => (source_Z_Q_U h v).1) x
    letI : Algebra (ZMod 2) F := ZMod.algebra F 2
    let H := graphLocalGroup (family P) x
    let π := ex.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 H))
    ∀ ρ : Representation (ZMod 2) SL(2,F) (Additive (Z (family P) x)),
      (∀ (l : H) (z : Additive (Z (family P) x)),
        ((ρ (π l) z).toMul : G) = (l : G) * z.toMul * (l : G)⁻¹) →
      ∀ E : Additive (Z (family P) x) ≃ₗ[ZMod 2] (Fin 2 → F),
      (∀ g z, E (ρ g z) = Matrix.mulVec g.val (E z)) →
      Nonempty (BinaryConjugationSection H (Z (family P) x) ⊥
        (((specialLinearNatural (k := F) 2).restrictScalars (k := ZMod 2)).comp π)) := by
  let := finite_endpoints h
  let := Z_elementary (family P) (fun v => (source_Z_Q_U h v).1) x
  let : Algebra (ZMod 2) F := ZMod.algebra F 2
  dsimp only
  intro ρ hact E hE
  let Γ := family P
  let H := graphLocalGroup Γ x
  let π := ex.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 H))
  let c := CommutingNontrivial.centerSection H (Z Γ x)
    (((source_Z_Q_U h x).1.trans (map_subtype_le _)).trans (core_le_graphLocalGroup h x))
    ((sylowGenerated_le _).trans (CommutingNontrivial.stabilizer_normalizes_Z Γ x)) π ρ hact
  let e : ρ.Equiv ((specialLinearNatural (k := F) 2).restrictScalars (k := ZMod 2)) :=
    Representation.Equiv.mk E (by intro g; apply LinearMap.ext; intro v; exact hE g v)
  exact ⟨c.relabel π e⟩

end CFSG.Quasithin.ChapterF.Source.DGS85.CommutingTrivial
