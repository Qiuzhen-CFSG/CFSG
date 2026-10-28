module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingOneProfile.BinaryBetaCartanReflection
public import Theory.GroupTheory.WeakBNPair.RegularTree.CyclicCartanReflection
public import Theory.SpecificGroups.SL2.OddBorelMarking
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingTrivial.TorusKernels

/-!
# Binary alpha reflections in the original four-path root class

In the elementary commuting distance-one branch with binary beta quotient,
the intrinsic alpha actor is the full endpoint stabilizer. Its full edge
Cartan is cyclic and embeds as the diagonal torus of the alpha SL₂ quotient.
Start with a specified edge-core involution outside the alpha two-core.
Conjugation in the quotient makes it antidiagonal; conjugation by the
local two-core then normalizes the prescribed Cartan while preserving the
specified involution class. The cyclic correction is proved in
`RegularTree.CyclicCartanReflection`.

An escaping elementary critical seed supplies the initial alpha involution.
Together with the binary beta reflection this constructs the original
four-path roots and their sharply transitive exit actions. A root involution
outside the full local kernel can then be used as the specified alpha class.
The construction lifts through the literal universal-tree homomorphism,
retaining the conjugator's original local-actor membership. The full Cartan
has trivial intersection with the alpha full local kernel, giving the
centralization clause of (14.2) without replacing that kernel by O₂.

These are original full-Borel source applications; no reflection, root
regularity, catalogue or quotient-kernel premise is supplied. The beta
prescribed-root choice, apartment exchange and complete marked recognition
remain separate obligations.

Source: Delgado--Goldschmidt--Stellmacher, *Groups and Graphs* (1985),
(11.7), pp.174--175, and (14.1)--(14.2), pp.210--211.
-/

public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Subgroup SimpleGraph SimpleGraph.PathTransitivePolygon
open Subgroup.CosetGeometry.RankTwo Theory.GroupTheory.AmalgamGraph
open Theory.GroupTheory.WeakBNPair.RegularTree
open scoped MatrixGroups IsMulCommutative
namespace CFSG.Quasithin.ChapterF.Source.DGS85.CommutingOneProfile
variable {G : Type*} [Group G] {P : Fin 2 → Subgroup G} {B : Subgroup G}

/-- A prescribed edge-core involution outside the vertex core has a
local-actor conjugate normalizing the same full edge Cartan. The Cartan's
containment in the actor is essential and is discharged at binary alpha. -/
theorem source_linear_actor_cartan_root_reflection
    (h : LocallyRankOneTriple P B)
    (hB : ∃ T : Sylow 2 B, (T : Subgroup B)=pCore 2 B)
    (hS : ∀ i, ∃ T : Sylow 2 (P i), (T : Subgroup (P i)).map (P i).subtype≤B)
    {v w : Vertex (family P)} (hvw : (graph (family P)).Adj v w)
    {k : Type*} [Field k] [Finite k] [CharP k 2]
    (e : (graphLocalGroup (family P) v ⧸ pCore 2 (graphLocalGroup (family P) v)) ≃* SL(2,k))
    (C : Subgroup G)
    (hCE : C≤stabilizer (family P) v ⊓ stabilizer (family P) w)
    (hCH : C≤graphLocalGroup (family P) v) (ho : Odd (Nat.card C))
    (hd : Disjoint C ((stabilizer (family P) v ⊓ stabilizer (family P) w).pCoreIn 2))
    (hg : C ⊔ (stabilizer (family P) v ⊓ stabilizer (family P) w).pCoreIn 2 =
      stabilizer (family P) v ⊓ stabilizer (family P) w)
    (x : G) (hx : x∈(stabilizer (family P) v ⊓ stabilizer (family P) w).pCoreIn 2)
    (hx2 : x*x=1) (hxQ : x∉Q (family P) v) :
    ∃ t∈graphLocalGroup (family P) v,
      t∈normalizer (C : Set G) ∧ t*t=1 ∧ t • v=v ∧ t • w≠w ∧
        ∃ g∈graphLocalGroup (family P) v, g*x*g⁻¹=t := by
  let _ := finite_endpoints h
  let Γ := family P
  let H := graphLocalGroup Γ v
  let E := stabilizer Γ v ⊓ stabilizer Γ w
  let U := E.pCoreIn 2
  let _ : Finite H := Finite.of_injective (inclusion (sylowGenerated_le _)) (inclusion_injective _)
  let K := C.subgroupOf H
  have hES : E≤normalizer (U : Set G) := E.le_normalizer.trans
    (normalizer_le_normalizer_characteristic_image E (pCore 2 E))
  obtain ⟨R,hR⟩ := CommutingTrivial.local_edge_sylow h hB hS hvw
  change (R : Subgroup H).map H.subtype=U at hR
  have hUH : U≤H := hR ▸ map_subtype_le _
  have hR' : (R : Subgroup H)=U.subgroupOf H := by
    apply Subgroup.map_injective H.subtype_injective
    rw [map_subgroupOf_eq_of_le hUH,hR]
  have hEN (l : H) (hl : (l : G)∈E) : l∈normalizer (R : Set H) := by
    change l∈normalizer ((R : Subgroup H) : Set H)
    rw [hR',←subgroupOf_normalizer_eq hUH]
    exact hES hl
  have hKN : K≤normalizer (R : Set H) := fun l hl => hEN l (hCE hl)
  obtain ⟨⟨f⟩,_⟩ := CommutingTrivial.edge_complement_local_torus h hB hS hvw e C hCE hd hg
  let j : K ≃* kˣ := (subgroupOfEquivOfLe hCH).trans
    ((MulEquiv.subgroupCongr (inf_eq_left.mpr hCH).symm).trans f)
  let _ : IsCyclic K := isCyclic_of_injective j.toMonoidHom j.injective
  have hoK : Odd (Nat.card K) := by
    rw [Nat.card_congr (subgroupOfEquivOfLe hCH).toEquiv]
    exact ho
  let q := e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 H))
  have hq : Function.Surjective q := e.surjective.comp (QuotientGroup.mk'_surjective _)
  have hker : q.ker=pCore 2 H := by
    rw [MonoidHom.ker_comp_of_injective _ _ e.injective,QuotientGroup.ker_mk']
  let Rq := R.mapSurjective hq
  obtain ⟨a,d,ha,hd⟩ := Matrix.SpecialLinearGroup.sylow_odd_subgroup_diagonal_coordinates
    Rq (K.map q) ((map_mono hKN).trans ((R : Subgroup H).le_normalizer_map q))
    (hoK.of_dvd_nat (K.card_map_dvd q))
  let φ := (MulAut.conj a).toMonoidHom.comp q
  have hφ : Function.Surjective φ := (MulAut.conj a).surjective.comp hq
  have hφker : φ.ker=pCore 2 H := by
    rw [MonoidHom.ker_comp_of_injective _ _ (MulAut.conj a).injective,hker]
  have hmark : (R : Subgroup H).map φ=Matrix.SpecialLinearGroup.upperUnipotent k := by
    rw [←Subgroup.map_map]
    exact ha
  let xH : H := ⟨x,hUH hx⟩
  have hxR : xH∈R := by change xH∈(R : Subgroup H); rw [hR']; exact hx
  obtain ⟨b,hb⟩ := (Matrix.SpecialLinearGroup.mem_upperUnipotent k (φ xH)).mp
    (hmark ▸ mem_map_of_mem φ hxR)
  have hxb : φ xH=NaturalCubic.upper b := hb.symm
  have hb0 : b≠0 := by
    intro he
    have hz : φ xH=1 := by rw [hxb,he]; simp [NaturalCubic.upper]
    have hxcore : xH∈pCore 2 H := hφker ▸ hz
    exact hxQ ((CommutingTrivial.graphLocalGroup_core h v).le (mem_map_of_mem H.subtype hxcore))
  obtain ⟨t,htN,ht2,htφ,g,hgt⟩ := exists_diagonal_cyclic_cartan_reflection φ hφ K
    (hφker ▸ (pCore_isPGroup (p := 2) (G := H))) hoK
    (by
      intro z hz
      refine ⟨(d ⟨q z,mem_map_of_mem q hz⟩ : k),(d _).ne_zero,?_⟩
      exact hd ⟨q z,mem_map_of_mem q hz⟩)
    xH (Subtype.ext hx2) b hb0 hxb
  have htC : (t:G)∈normalizer (C : Set G) := by
    have hh := K.le_normalizer_map H.subtype (mem_map_of_mem H.subtype htN)
    rwa [map_subgroupOf_eq_of_le hCH] at hh
  refine ⟨t,t.property,htC,congrArg Subtype.val ht2,sylowGenerated_le _ t.property,?_,
    g,g.property,congrArg Subtype.val hgt⟩
  intro htfix
  have htE : (t:G)∈E := ⟨sylowGenerated_le _ t.property,htfix⟩
  have htU := (R : Subgroup H).le_normalizer_map φ (mem_map_of_mem φ (hEN t htE))
  rw [hmark] at htU
  have hz := (Matrix.SpecialLinearGroup.mem_rankOneBorel_iff (φ t)).mp htU
  rw [htφ,NaturalCubic.braid_matrix b hb0] at hz
  exact (inv_ne_zero hb0) hz


section Original
open Reduction NoncommutingProfile CommutingNontrivial
open Theory.GroupTheory RankTwoAmalgam OriginalExtension SuzukiContainment
open CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.ApartmentExchange
open ReducedCartan
variable {L : Fin 2 → Subgroup G} {S : Subgroup G}
local notation "F" => reducedFamily L S
local notation "A" => reducedAmalgam L S
local notation "T" => Universal.cosetFamily A
local notation "G₀" => Reduction.G₀ L S
local notation "α" => base F false
local notation "β" => base F true
variable (h : HypothesisF11 L S)
    (hc : IsCriticalPair (reducedFamily L S)
      (base (reducedFamily L S) false) (base (reducedFamily L S) true))
    (hb : DGS85.b (reducedFamily L S)=1)
    (hcomm : ⁅Z (reducedFamily L S) (base (reducedFamily L S) false),
      Z (reducedFamily L S) (base (reducedFamily L S) true)⁆=⊥)
    (helem : ∃ hN : (((Q (reducedFamily L S) (base (reducedFamily L S) true)).map
        (Reduction.G₀ L S).subtype).subgroupOf
        (twoCore (commonBorel L S))).Normal,
      letI := hN
      IsElementaryAbelian 2 (twoCore (commonBorel L S) ⧸
        ((Q (reducedFamily L S) (base (reducedFamily L S) true)).map
          (Reduction.G₀ L S).subtype).subgroupOf (twoCore (commonBorel L S))))
    (hbinary : ClassicalGroup.IsPSL
      ((graphLocalGroup (reducedFamily L S) (base (reducedFamily L S) true)).map
        (Reduction.G₀ L S).subtype ⧸
      pCore 2 ((graphLocalGroup (reducedFamily L S) (base (reducedFamily L S) true)).map
        (Reduction.G₀ L S).subtype)) 2 2)
include h hc hb hcomm helem hbinary


omit h hc hb hcomm helem in
private theorem original_binary_beta_marking :
    Nonempty ((graphLocalGroup F β ⧸ pCore 2 (graphLocalGroup F β)) ≃* SL(2,ZMod 2)) := by
  let H := graphLocalGroup F β
  let j := H.equivMapOfInjective (G₀).subtype (G₀).subtype_injective
  let e := QuotientGroup.congr _ _ j (pCore_map_iso 2 j)
  have mb : ClassicalGroup.IsPSL (H ⧸ pCore 2 H) 2 2 := hbinary.of_mulEquiv e
  obtain ⟨k,fk,fink,hk,⟨eb⟩⟩ := mb
  let _ := fk
  let _ := fink
  let _ : Fintype k := Fintype.ofFinite k
  let _ : CharP k 2 := charP_of_card_eq_prime_pow
    (show Fintype.card k=2^1 by simpa only [Nat.card_eq_fintype_card,pow_one] using hk)
  let eSL : (H ⧸ pCore 2 H) ≃* SL(2,k) :=
    eb.trans (MulEquiv.ofBijective (BenderSuzuki.Converse.pi k)
      ⟨BenderSuzuki.Converse.pi_injective,BenderSuzuki.Converse.pi_surjective⟩).symm
  let ek := ZMod.ringEquivOfPrime k Nat.prime_two
    (by simpa only [Nat.card_eq_fintype_card] using hk)
  let f := Matrix.SpecialLinearGroup.map (n := Fin 2) ek.symm.toRingHom
  have hf : Function.Injective f := by
    intro a b hab
    ext i j
    exact ek.symm.injective (congrArg (fun z : SL(2,ZMod 2) => z.val i j) hab)
  have hcard : Nat.card SL(2,k)=Nat.card SL(2,ZMod 2) := by
    rw [BenderSuzuki.External.huppert614_card_specialLinearGroup,
      BenderSuzuki.External.huppert614_card_specialLinearGroup,hk]
    simp
  exact ⟨eSL.trans (MulEquiv.ofBijective f ((Nat.bijective_iff_injective_and_card f).mpr ⟨hf,hcard⟩))⟩

/-- At the binary alpha endpoint the full Cartan has trivial intersection
with the full local permutation kernel. This uses the nonbinary alpha
quotient, and does not identify the permutation kernel with the two-core. -/
theorem original_elementary_binary_alpha_cartan_kernel_eq_bot
    (C : Subgroup G₀) (hCE : C≤stabilizer F α ⊓ stabilizer F β)
    (ho : Odd (Nat.card C)) : C ⊓ U F α=⊥ := by
  let _ : ∀ i, Finite (F i) := finite_endpoints (reduced_triple h)
  let d := reducedFullEarlierLocalTheorems h
  let eb := Classical.choice (original_binary_beta_marking hbinary)
  have hfull : graphLocalGroup F α=stabilizer F α :=
    reduced_binary_alpha_local_eq_full h d (source_critical_one_adjacent hc hb) eb
  obtain ⟨m,hm,_,markA,_⟩ := original_borel_elementary_orders_and_paths_of_source h hc hb hcomm helem
  obtain ⟨k,fk,fink,hk,⟨ea⟩⟩ := markA
  let _ := fk
  let _ := fink
  let _ : Fintype k := Fintype.ofFinite k
  let _ : CharP k 2 := charP_of_card_eq_prime_pow
    (by simpa only [Nat.card_eq_fintype_card] using hk)
  let H := graphLocalGroup F α
  let j := H.equivMapOfInjective (G₀).subtype (G₀).subtype_injective
  let e := (QuotientGroup.congr _ _ j (pCore_map_iso 2 j)).trans
    (ea.trans (MulEquiv.ofBijective (BenderSuzuki.Converse.pi k)
      ⟨BenderSuzuki.Converse.pi_injective,BenderSuzuki.Converse.pi_surjective⟩).symm)
  have hfour : 4≤Nat.card k := by
    rw [hk]
    exact Nat.pow_le_pow_right (by decide : 1≤(2:ℕ)) (by omega : 2≤2*m)
  have hJU : H ⊓ U F α=Q F α := CommutingTrivial.nonbinary_local_kernel_intersection
    (reduced_triple h) (reduced_borel_core_sylow h) (reduced_vertex_sylow h)
    (source_critical_one_adjacent hc hb) e hfour
  let _ : Finite (Q F α) := Finite.of_injective (inclusion (Q_le_stabilizer F α))
    (inclusion_injective _)
  have hd : Disjoint C (Q F α) := by
    have hpQ : IsPGroup 2 (Q F α) := isPGroup_pCoreIn 2 _
    obtain ⟨r,hr⟩ := hpQ.exists_card_eq
    apply disjoint_of_coprime_natCard
    change Nat.card (Q F α)=2^r at hr
    rw [hr]
    exact ho.coprime_two_right.pow_right r
  have hCH : C≤H := by
    change C≤graphLocalGroup F α
    rw [hfull]
    exact hCE.trans inf_le_left
  apply le_antisymm ?_ bot_le
  intro z hz
  exact disjoint_def.mp hd hz.1 (hJU.le ⟨hCH hz.1,hz.2⟩)

/-- At the original binary alpha endpoint, every specified edge-core involution
outside the vertex core has a local-actor conjugate normalizing the full Cartan. -/
theorem original_elementary_binary_alpha_root_reflection
    (C : Subgroup G₀)
    (hCE : C≤stabilizer F α ⊓ stabilizer F β) (ho : Odd (Nat.card C))
    (hd : Disjoint C ((stabilizer F α ⊓ stabilizer F β).pCoreIn 2))
    (hg : C ⊔ (stabilizer F α ⊓ stabilizer F β).pCoreIn 2=stabilizer F α ⊓ stabilizer F β)
    (x : G₀) (hx : x∈(stabilizer F α ⊓ stabilizer F β).pCoreIn 2)
    (hx2 : x*x=1) (hxQ : x∉Q F α) :
    ∃ t∈graphLocalGroup F α, t∈normalizer (C : Set G₀) ∧ t*t=1 ∧
      t • α=α ∧ t • β≠β ∧ ∃ g∈graphLocalGroup F α, g*x*g⁻¹=t := by
  let d := reducedFullEarlierLocalTheorems h
  let eb := Classical.choice (original_binary_beta_marking hbinary)
  have hfull : graphLocalGroup F α=stabilizer F α :=
    reduced_binary_alpha_local_eq_full h d (source_critical_one_adjacent hc hb) eb
  obtain ⟨m,hm,_,markA,_⟩ := original_borel_elementary_orders_and_paths_of_source h hc hb hcomm helem
  obtain ⟨k,fk,fink,hk,⟨ea⟩⟩ := markA
  let _ := fk
  let _ := fink
  let _ : Fintype k := Fintype.ofFinite k
  let _ : CharP k 2 := charP_of_card_eq_prime_pow
    (by simpa only [Nat.card_eq_fintype_card] using hk)
  let H := graphLocalGroup F α
  let j := H.equivMapOfInjective (G₀).subtype (G₀).subtype_injective
  let e := (QuotientGroup.congr _ _ j (pCore_map_iso 2 j)).trans
    (ea.trans (MulEquiv.ofBijective (BenderSuzuki.Converse.pi k)
      ⟨BenderSuzuki.Converse.pi_injective,BenderSuzuki.Converse.pi_surjective⟩).symm)
  exact source_linear_actor_cartan_root_reflection (reduced_triple h)
    (reduced_borel_core_sylow h) (reduced_vertex_sylow h) (source_critical_one_adjacent hc hb)
    e C hCE (hfull.symm ▸ hCE.trans inf_le_left) ho hd hg x hx hx2 hxQ

/-- A neighboring elementary seed constructs the initial involution; no
quotient-reflection, natural-kernel or fixed-point-free Cartan premise is supplied. -/
theorem original_elementary_binary_alpha_cartan_reflection
    (C : Subgroup G₀)
    (hCE : C≤stabilizer F α ⊓ stabilizer F β) (ho : Odd (Nat.card C))
    (hd : Disjoint C ((stabilizer F α ⊓ stabilizer F β).pCoreIn 2))
    (hg : C ⊔ (stabilizer F α ⊓ stabilizer F β).pCoreIn 2=stabilizer F α ⊓ stabilizer F β) :
    ∃ t∈graphLocalGroup F α, t∈normalizer (C : Set G₀) ∧ t*t=1 ∧
      t • α=α ∧ t • β≠β := by
  let H := reduced_triple h
  let d := reducedFullEarlierLocalTheorems h
  let _ : ∀ i, Finite (F i) := finite_endpoints H
  have hab := source_critical_one_adjacent hc hb
  have hval : 3≤Nat.card ((graph F).neighborSet β) := by
    rw [card_neighbors_of_indices F (fun i => ((F (!i)).subgroupOf (F i)).index) (fun _ => rfl)]
    exact source_valence_ge_three H (reduced_vertex_sylow h) true
  obtain ⟨c,hbc,hca⟩ := Set.exists_ne_of_one_lt_ncard (s := (graph F).neighborSet β)
    (by rw [←Nat.card_coe_set_eq]; omega) α
  obtain ⟨g,hgb,hgac⟩ := locally_transitive F hab.symm hbc
  have hc' := criticalPair_translate F hc g
  rw [hgac,show g • β=β from hgb] at hc'
  let eb := Classical.choice (original_binary_beta_marking hbinary)
  have Mb : IsRankOneModel (d.localGroup β ⧸ pCore 2 (d.localGroup β)) := by
    apply IsRankOneModel.linear 1 (by decide)
    refine ⟨ZMod 2,inferInstance,inferInstance,by simp,?_⟩
    exact ⟨eb.trans (MulEquiv.ofBijective (BenderSuzuki.Converse.pi (ZMod 2))
      ⟨BenderSuzuki.Converse.pi_injective,BenderSuzuki.Converse.pi_surjective⟩)⟩
  have hesc := (source_rankOne_seed_escape H (reduced_borel_core_sylow h) d
    hc' hb hab.symm hca Mb).1
  obtain ⟨x,hx,hxQ⟩ := Set.not_subset.mp hesc
  let _ := source_center_elementary H c
  have hx2 : x*x=1 := by simpa only [pow_two] using elemPow_eq_one_of_isElementaryAbelian (p := 2) x hx.1
  have hxE : x∈(stabilizer F α ⊓ stabilizer F β).pCoreIn 2 := by
    have hh := Noncommuting.graph_Q_le_edgeCore H hab.symm hx.2
    simpa only [inf_comm] using hh
  obtain ⟨t,ht,htC,ht2,hta,htb,_⟩ := original_elementary_binary_alpha_root_reflection
    h hc hb hcomm helem hbinary C hCE ho hd hg x hxE hx2 hxQ
  exact ⟨t,ht,htC,ht2,hta,htb⟩

/-- The original alpha universal endpoint contains the required involution,
normalizing the same prescribed full Cartan. -/
theorem original_elementary_binary_alpha_tree_reflection
    (c : CompatibleCartans L (reducedSylow L S)) :
    ∃ t : (reducedAmalgam L S).Universal, t • base T false = base T false ∧
      t • base T true ≠ base T true ∧ t*t=1 ∧
      t ∈ normalizer (cartan c : Set (reducedAmalgam L S).Universal) := by
  let φ := bOne_tree_map h
  let cov := bOne_tree_cover h
  let C := (cartan c).map φ
  let U := (twoGroup L S).map φ
  let E := F false ⊓ F true
  let : Finite (F false) := (finite_endpoints (reduced_triple h)) false
  let : Finite (F true) := (finite_endpoints (reduced_triple h)) true
  let _ : Finite E := Finite.of_injective (inclusion (show E ≤ F false from inf_le_left))
    (inclusion_injective _)
  let _ : Finite (E.pCoreIn 2) := Finite.of_injective (inclusion (pCoreIn_le 2 E))
    (inclusion_injective _)
  let _ := cartan_abelian h c
  let _ : IsMulCommutative C := inferInstanceAs (IsMulCommutative ((cartan c).map φ))
  have hmiddle : originalMiddle A=T false ⊓ T true :=
    (Universal.overlap_eq A (inclusion_injective (commonBorel_le_parabolic 0))
      (inclusion_injective (commonBorel_le_parabolic 1))).symm
  have hmapE : (originalMiddle A).map φ = E := by
    rw [hmiddle]
    exact cov.map_inf
  have hCE : C ≤ E := hmapE ▸ map_mono (cartan_le c)
  have hUE : U ≤ E := hmapE ▸ map_mono (twoGroup_le (L := L) (S := S))
  have hUnorm : E ≤ normalizer (U : Set G₀) := by
    rw [←hmapE]
    exact (map_mono (twoGroup_normalized h)).trans ((twoGroup L S).le_normalizer_map φ)
  have hUcore : U ≤ E.pCoreIn 2 :=
    le_pCoreIn_of_normalizes ((twoGroup_isTwo h).map φ) hUE hUnorm
  have ho : Odd (Nat.card C) := (Nat.coprime_two_left.mp (cartan_odd c)).of_dvd_nat
    ((cartan c).card_map_dvd φ)
  have hd : Disjoint C (E.pCoreIn 2) := by
    obtain ⟨m,hm⟩ := (isPGroup_pCoreIn 2 E).exists_card_eq
    exact disjoint_of_coprime_natCard (by rw [hm]; exact ho.coprime_two_right.pow_right m)
  have hg : C ⊔ E.pCoreIn 2 = E := by
    apply le_antisymm (sup_le hCE (pCoreIn_le 2 E))
    have he := congrArg (Subgroup.map φ) (factorization c)
    rw [Subgroup.map_sup,hmapE] at he
    calc
      E = U ⊔ C := he.symm
      _ ≤ C ⊔ E.pCoreIn 2 :=
        sup_le (hUcore.trans le_sup_right) le_sup_left
  have hEi : E=stabilizer F α ⊓ stabilizer F β := by
    have ha : stabilizer F α=F false := Subgroup.CosetGeometry.stabilizer_base F false
    have hb : stabilizer F β=F true := Subgroup.CosetGeometry.stabilizer_base F true
    rw [ha,hb]
  obtain ⟨g,_,hgC,hgsq,hgfix,hgmove⟩ := original_elementary_binary_alpha_cartan_reflection
    h hc hb hcomm helem hbinary C (hEi ▸ hCE) ho (hEi ▸ hd) (hEi ▸ hg)
  have hgFi : g ∈ F false := by
    rw [←Subgroup.CosetGeometry.stabilizer_base F false]
    exact hgfix
  have hgimage : g ∈ (T false).map φ := (cov.map_eq false).symm ▸ hgFi
  obtain ⟨t,ht,htg⟩ := hgimage
  have hfix : t • base T false = base T false := by
    have hh := ht
    rw [←Subgroup.CosetGeometry.stabilizer_base T false] at hh
    exact hh
  have hmove : t • base T true ≠ base T true := by
    intro he
    have hh := congrArg cov.vertex he
    apply hgmove
    have hh' : (bOne_tree_map h) t • base (reducedFamily L S) true =
        base (reducedFamily L S) true := by
      simpa only [cov.vertex_smul, cov.vertex_base] using hh
    change φ t • base F true = base F true at hh'
    rw [← htg]
    exact hh'
  have hsq : t*t=1 := by
    have he : φ (t*t) = φ 1 := by rw [map_mul,htg,hgsq,map_one]
    exact congrArg Subtype.val (cov.injective false
      (a₁ := ⟨t*t,(T false).mul_mem ht ht⟩) (a₂ := 1) he)
  have hKi : cartan c ≤ T false := (cartan_le c).trans (hmiddle ▸ inf_le_left)
  let Ki := (cartan c).subgroupOf (T false)
  let f : T false →* G₀ := φ.comp (T false).subtype
  have hf : Function.Injective f := cov.injective false
  have hKmap : Ki.map f = C := by
    change Ki.map (φ.comp (T false).subtype) = C
    rw [←Subgroup.map_map,map_subgroupOf_eq_of_le hKi]
  have htKi : (⟨t,ht⟩ : T false) ∈ normalizer (Ki : Set (T false)) := by
    have hh : (⟨t,ht⟩ : T false) ∈ (normalizer (Ki.map f : Set G₀)).comap f := by
      change f ⟨t,ht⟩ ∈ normalizer (Ki.map f : Set G₀)
      rw [hKmap]
      exact htg.symm ▸ hgC
    rw [comap_normalizer_eq_of_le_range (map_le_range _ _),
      comap_map_eq_self_of_injective hf] at hh
    exact hh
  have hnorm := Ki.le_normalizer_map (T false).subtype (mem_map_of_mem (T false).subtype htKi)
  rw [map_subgroupOf_eq_of_le hKi] at hnorm
  exact ⟨t,hfix,hmove,hsq,hnorm⟩


/-- Both constructed binary reflections normalize the same original full Cartan. -/
theorem original_elementary_binary_tree_reflections
    (c : CompatibleCartans L (reducedSylow L S)) :
    ∃ t : Bool → (A).Universal,
      (∀ i, t i • base T i=base T i) ∧
      (∀ i, t i • base T (!i)≠base T (!i)) ∧
      (∀ i, t i*t i=1) ∧
      (∀ i, t i∈normalizer (cartan c : Set (A).Universal)) := by
  have hex (i : Bool) : ∃ t : (A).Universal,
      t • base T i=base T i ∧ t • base T (!i)≠base T (!i) ∧
      t*t=1 ∧ t∈normalizer (cartan c : Set (A).Universal) := by
    cases i
    · exact original_elementary_binary_alpha_tree_reflection h hc hb hcomm helem hbinary c
    · obtain ⟨t,ht,hm,hs,hn,_⟩ := original_elementary_binary_beta_tree_reflection
        h hc hb hcomm helem hbinary c
      exact ⟨t,ht,hm,hs,Subgroup.centralizer_le_normalizer _ hn⟩
  choose t ht hm hs hn using hex
  exact ⟨t,ht,hm,hs,hn⟩
/-- Construct the two four-path roots from the original binary elementary
source. The same chosen full Cartan and the actual involutions are retained;
each root acts sharply transitively on its marked exits. -/
theorem original_elementary_binary_path_roots :
    ∃ ρ : Bool → LocalRootAction (X := (reducedAmalgam L S).Universal)
        (sourceGraph (reducedAmalgam L S)),
      (∀ i, (ρ i).a = base T i) ∧
      (∀ i, (ρ i).b = base T (!i)) ∧
      (∀ i, (ρ i).reflection ∈ normalizer
        (cartan (chosenCartans h) : Set (reducedAmalgam L S).Universal)) ∧
      (∀ i, (ρ i).reflection * (ρ i).reflection = 1) ∧
      (∀ i, ∃ d, ∃ p : (sourceGraph (reducedAmalgam L S)).Walk d (base T i),
        p.IsPath ∧ p.length = 4 ∧ p.penultimate = base T (!i) ∧
        (ρ i).root = (pathFixer (X := (reducedAmalgam L S).Universal) p).pCoreIn 2 ∧
        cartan (chosenCartans h) ≤ pathFixer (X := (reducedAmalgam L S).Universal) p ∧
        ∀ z ∈ p.support, z ∈ cartanApartment (reducedAmalgam L S)
          (apartmentGroup (chosenCartans h) ρ)) ∧
      (∀ i z, (sourceGraph (reducedAmalgam L S)).Adj (ρ i).a z → z ≠ (ρ i).b →
        ∃! x : (ρ i).root, (x : (reducedAmalgam L S).Universal) • (ρ i).c = z) := by
  let c := chosenCartans h
  obtain ⟨t,htfix,htmove,htsq,htnorm⟩ :=
    original_elementary_binary_tree_reflections h hc hb hcomm helem hbinary c
  have hpath := original_elementary_tree_path_profile h hc hb hcomm
    (original_borel_elementary_alpha_model h hc hb helem)
    (original_borel_elementary_beta_model h helem) helem
  have hthick := original_source_tree_thickness h t
  let ρ := pathRoots h c 4 (by decide) t htfix htmove htsq htnorm hpath.1 hthick
  refine ⟨ρ,?_,?_,?_,?_,?_,?_⟩
  · exact pathRoots_a h c 4 (by decide) t htfix htmove htsq htnorm hpath.1 hthick
  · exact pathRoots_b h c 4 (by decide) t htfix htmove htsq htnorm hpath.1 hthick
  · exact pathRoots_normalizes h c 4 (by decide) t htfix htmove htsq htnorm hpath.1 hthick
  · exact pathRoots_square h c 4 (by decide) t htfix htmove htsq htnorm hpath.1 hthick
  · intro i
    let p := reflectionPath c t htfix htmove htnorm 4 (by decide) i
    exact ⟨p.start,p.walk,p.isPath,p.length_eq,p.previous,rfl,p.fixed,
      pathRoots_supported h c 4 (by decide) t htfix htmove htsq htnorm hpath.1 hthick i⟩
  · exact pathRoots_sharply_transitive h c 4 (by decide) t htfix htmove htsq htnorm
      hpath.1 hthick hpath.2

/-- Preserve the conjugacy class of any escaping involution in a prescribed
path root when lifting the alpha reflection through the original tree cover. -/
theorem original_elementary_binary_alpha_prescribed_root_reflection
    (c : CompatibleCartans L (reducedSylow L S))
    {d : SourceVertex A} (p : (sourceGraph A).Walk d (base T false))
    (hpPrev : p.penultimate=base T true)
    (x : (A).Universal) (hx : x∈pathRoot (X := (A).Universal) p)
    (hx2 : x*x=1) (hxU : x∉ballKernel T (base T false) 1) :
    ∃ t : (A).Universal, t • base T false=base T false ∧
      t • base T true≠base T true ∧ t*t=1 ∧
      t∈normalizer (cartan c : Set (A).Universal) ∧
      ∃ g∈T false, (bOne_tree_map h) g∈graphLocalGroup F α ∧ g*x*g⁻¹=t := by
  let φ := bOne_tree_map h
  let cov := bOne_tree_cover h
  let C := (cartan c).map φ
  let U := (twoGroup L S).map φ
  let E := F false ⊓ F true
  let : Finite (F false) := (finite_endpoints (reduced_triple h)) false
  let : Finite (F true) := (finite_endpoints (reduced_triple h)) true
  let _ : Finite E := Finite.of_injective (inclusion (show E ≤ F false from inf_le_left))
    (inclusion_injective _)
  let _ : Finite (E.pCoreIn 2) := Finite.of_injective (inclusion (pCoreIn_le 2 E))
    (inclusion_injective _)
  let _ := cartan_abelian h c
  let _ : IsMulCommutative C := inferInstanceAs (IsMulCommutative ((cartan c).map φ))
  have hmiddle : originalMiddle A=T false ⊓ T true :=
    (Universal.overlap_eq A (inclusion_injective (commonBorel_le_parabolic 0))
      (inclusion_injective (commonBorel_le_parabolic 1))).symm
  have hmapE : (originalMiddle A).map φ = E := by
    rw [hmiddle]
    exact cov.map_inf
  have hCE : C ≤ E := hmapE ▸ map_mono (cartan_le c)
  have hUE : U ≤ E := hmapE ▸ map_mono (twoGroup_le (L := L) (S := S))
  have hUnorm : E ≤ normalizer (U : Set G₀) := by
    rw [←hmapE]
    exact (map_mono (twoGroup_normalized h)).trans ((twoGroup L S).le_normalizer_map φ)
  have hUcore : U ≤ E.pCoreIn 2 :=
    le_pCoreIn_of_normalizes ((twoGroup_isTwo h).map φ) hUE hUnorm
  have ho : Odd (Nat.card C) := (Nat.coprime_two_left.mp (cartan_odd c)).of_dvd_nat
    ((cartan c).card_map_dvd φ)
  have hd : Disjoint C (E.pCoreIn 2) := by
    obtain ⟨m,hm⟩ := (isPGroup_pCoreIn 2 E).exists_card_eq
    exact disjoint_of_coprime_natCard (by rw [hm]; exact ho.coprime_two_right.pow_right m)
  have hg : C ⊔ E.pCoreIn 2 = E := by
    apply le_antisymm (sup_le hCE (pCoreIn_le 2 E))
    have he := congrArg (Subgroup.map φ) (factorization c)
    rw [Subgroup.map_sup,hmapE] at he
    calc
      E = U ⊔ C := he.symm
      _ ≤ C ⊔ E.pCoreIn 2 :=
        sup_le (hUcore.trans le_sup_right) le_sup_left
  have hEi : E=stabilizer F α ⊓ stabilizer F β := by
    have ha : stabilizer F α=F false := Subgroup.CosetGeometry.stabilizer_base F false
    have hb : stabilizer F β=F true := Subgroup.CosetGeometry.stabilizer_base F true
    rw [ha,hb]
  have hxfix := pathRoot_fixes p hx
  have hxa : x • base T false=base T false := hxfix.1
  have hxb : x • base T true=base T true := hpPrev ▸ hxfix.2
  have hRx : (pathRoot (X := (A).Universal) p).map φ ≤ E := by
    rintro z ⟨y,hy,rfl⟩
    have hya : y • base T false=base T false := (pathRoot_fixes p hy).1
    have hyb : y • base T true=base T true := hpPrev ▸ (pathRoot_fixes p hy).2
    have hya' := congrArg cov.vertex hya
    have hyb' := congrArg cov.vertex hyb
    constructor
    · rw [←Subgroup.CosetGeometry.stabilizer_base F false]
      change φ y • base F false=base F false
      simpa only [cov.vertex_smul,cov.vertex_base] using hya'
    · rw [←Subgroup.CosetGeometry.stabilizer_base F true]
      change φ y • base F true=base F true
      simpa only [cov.vertex_smul,cov.vertex_base] using hyb'
  have hxE : φ x∈(stabilizer F α ⊓ stabilizer F β).pCoreIn 2 := by
    rw [←hEi]
    apply pGroup_le_core_of_core_sylow E ((pathRoot (X := (A).Universal) p).map φ)
      hRx ((pathRoot_isTwo p).map φ)
    · exact hEi.symm ▸ source_edge_core_sylow (reduced_triple h)
        (reduced_borel_core_sylow h) (source_critical_one_adjacent hc hb)
    · exact mem_map_of_mem φ hx
  have hxQ : φ x∉Q F α := by
    intro he
    have hu : φ x∈ballKernel F (cov.vertex (base T false)) 1 := by
      rw [cov.vertex_base]
      exact (source_Z_Q_U (reduced_triple h) α).2 he
    exact hxU (cov.ballKernel_lift (base T false) 1 x hxa hu)
  obtain ⟨g,_,hgC,hgsq,hgfix,hgmove,z,hzJ,hzx⟩ := original_elementary_binary_alpha_root_reflection
    h hc hb hcomm helem hbinary C (hEi ▸ hCE) ho (hEi ▸ hd) (hEi ▸ hg)
      (φ x) hxE (by rw [←map_mul,hx2,map_one]) hxQ
  have hgFi : g ∈ F false := by
    rw [←Subgroup.CosetGeometry.stabilizer_base F false]
    exact hgfix
  have hgimage : g ∈ (T false).map φ := (cov.map_eq false).symm ▸ hgFi
  obtain ⟨t,ht,htg⟩ := hgimage
  have hfix : t • base T false = base T false := by
    have hh := ht
    rw [←Subgroup.CosetGeometry.stabilizer_base T false] at hh
    exact hh
  have hmove : t • base T true ≠ base T true := by
    intro he
    have hh := congrArg cov.vertex he
    apply hgmove
    have hh' : (bOne_tree_map h) t • base (reducedFamily L S) true =
        base (reducedFamily L S) true := by
      simpa only [cov.vertex_smul, cov.vertex_base] using hh
    change φ t • base F true = base F true at hh'
    rw [← htg]
    exact hh'
  have hsq : t*t=1 := by
    have he : φ (t*t) = φ 1 := by rw [map_mul,htg,hgsq,map_one]
    exact congrArg Subtype.val (cov.injective false
      (a₁ := ⟨t*t,(T false).mul_mem ht ht⟩) (a₂ := 1) he)
  have hKi : cartan c ≤ T false := (cartan_le c).trans (hmiddle ▸ inf_le_left)
  let Ki := (cartan c).subgroupOf (T false)
  let f : T false →* G₀ := φ.comp (T false).subtype
  have hf : Function.Injective f := cov.injective false
  have hKmap : Ki.map f = C := by
    change Ki.map (φ.comp (T false).subtype) = C
    rw [←Subgroup.map_map,map_subgroupOf_eq_of_le hKi]
  have htKi : (⟨t,ht⟩ : T false) ∈ normalizer (Ki : Set (T false)) := by
    have hh : (⟨t,ht⟩ : T false) ∈ (normalizer (Ki.map f : Set G₀)).comap f := by
      change f ⟨t,ht⟩ ∈ normalizer (Ki.map f : Set G₀)
      rw [hKmap]
      exact htg.symm ▸ hgC
    rw [comap_normalizer_eq_of_le_range (map_le_range _ _),
      comap_map_eq_self_of_injective hf] at hh
    exact hh
  have hnorm := Ki.le_normalizer_map (T false).subtype (mem_map_of_mem (T false).subtype htKi)
  rw [map_subgroupOf_eq_of_le hKi] at hnorm
  have hzFi : z∈F false := by
    rw [←Subgroup.CosetGeometry.stabilizer_base F false]
    exact sylowGenerated_le _ hzJ
  obtain ⟨y,hy,hyz⟩ := (cov.map_eq false).symm ▸ hzFi
  have hxFi : x∈T false := by
    rw [←Subgroup.CosetGeometry.stabilizer_base T false]
    exact hxa
  have he : φ (y*x*y⁻¹)=φ t := by
    rw [map_mul,map_mul,map_inv,hyz,htg]
    exact hzx
  have hconj : y*x*y⁻¹=t := congrArg Subtype.val (cov.injective false
    (a₁ := ⟨y*x*y⁻¹,(T false).mul_mem ((T false).mul_mem hy hxFi) ((T false).inv_mem hy)⟩)
    (a₂ := ⟨t,ht⟩) he)
  exact ⟨t,hfix,hmove,hsq,hnorm,y,hy,hyz.symm ▸ hzJ,hconj⟩


/-- The same full-Cartan kernel clause holds through the literal universal
tree map; in particular every alpha reflection centralizes this intersection. -/
theorem original_elementary_binary_alpha_tree_cartan_kernel_eq_bot
    (c : CompatibleCartans L (reducedSylow L S)) :
    cartan c ⊓ (U F α).comap (bOne_tree_map h)=⊥ := by
  let φ := bOne_tree_map h
  let cov := bOne_tree_cover h
  have hmiddle : originalMiddle A=T false ⊓ T true :=
    (Universal.overlap_eq A (inclusion_injective (commonBorel_le_parabolic 0))
      (inclusion_injective (commonBorel_le_parabolic 1))).symm
  have hCE : (cartan c).map φ≤stabilizer F α ⊓ stabilizer F β := by
    have hh := map_mono (cartan_le c) (f := φ)
    rw [hmiddle,cov.map_inf] at hh
    simpa only [Subgroup.CosetGeometry.stabilizer_base] using hh
  have ho : Odd (Nat.card ((cartan c).map φ)) :=
    (Nat.coprime_two_left.mp (cartan_odd c)).of_dvd_nat ((cartan c).card_map_dvd φ)
  have hkernel := original_elementary_binary_alpha_cartan_kernel_eq_bot
    h hc hb hcomm helem hbinary ((cartan c).map φ) hCE ho
  apply le_antisymm ?_ bot_le
  intro k hk
  have hm : φ k=1 := hkernel.le ⟨mem_map_of_mem φ hk.1,hk.2⟩
  have hkT : k∈T false := (hmiddle ▸ cartan_le c hk.1).1
  exact congrArg Subtype.val (cov.injective false (a₁ := ⟨k,hkT⟩) (a₂ := 1)
    (by change φ k=φ 1; simpa only [map_one] using hm))

/-- The genuine original binary source supplies a four-path root involution
and a reflection in its alpha-local conjugacy class, with no reflection or
path-regularity premise. The path fixer and covering maps remain literal. -/
theorem original_elementary_binary_alpha_four_path_reflection
    (c : CompatibleCartans L (reducedSylow L S)) :
    ∃ d, ∃ p : (sourceGraph A).Walk d (base T false),
      p.IsPath ∧ p.length=4 ∧ p.penultimate=base T true ∧
      cartan c≤pathFixer (X := (A).Universal) p ∧
      ∃ x∈pathRoot (X := (A).Universal) p, orderOf x=2 ∧
      ∃ t : (A).Universal, t • base T false=base T false ∧
        t • base T true≠base T true ∧ t*t=1 ∧
        t∈normalizer (cartan c : Set (A).Universal) ∧
        (∀ k∈cartan c ⊓ (U F α).comap (bOne_tree_map h), Commute t k) ∧
        ∃ g∈T false, (bOne_tree_map h) g∈graphLocalGroup F α ∧ g*x*g⁻¹=t := by
  obtain ⟨t,htfix,htmove,htsq,htnorm⟩ :=
    original_elementary_binary_tree_reflections h hc hb hcomm helem hbinary c
  have hpath := original_elementary_tree_path_profile h hc hb hcomm
    (original_borel_elementary_alpha_model h hc hb helem)
    (original_borel_elementary_beta_model h helem) helem
  have hthick := original_source_tree_thickness h t
  let p := reflectionPath c t htfix htmove htnorm 4 (by decide) false
  obtain ⟨x,hx,hxo,hxU⟩ := pathRoots_exists_involution_outside_localKernel
    h c 4 (by decide) t htfix htmove htsq htnorm hpath.1 hthick hpath.2 false
  change x∈pathRoot (X := (A).Universal) p.walk at hx
  have hx2 : x*x=1 := by simpa only [hxo,pow_two] using pow_orderOf_eq_one x
  obtain ⟨u,hua,hub,hu2,huC,g,hg,hgJ,hgxu⟩ :=
    original_elementary_binary_alpha_prescribed_root_reflection h hc hb hcomm helem hbinary
      c p.walk p.previous x hx hx2 hxU
  refine ⟨p.start,p.walk,p.isPath,p.length_eq,p.previous,p.fixed,
    x,hx,hxo,u,hua,hub,hu2,huC,?_,g,hg,hgJ,hgxu⟩
  intro k hk
  have he : k=1 := (original_elementary_binary_alpha_tree_cartan_kernel_eq_bot
    h hc hb hcomm helem hbinary c).le hk
  rw [he]
  exact Commute.one_right u

end Original
end CFSG.Quasithin.ChapterF.Source.DGS85.CommutingOneProfile
