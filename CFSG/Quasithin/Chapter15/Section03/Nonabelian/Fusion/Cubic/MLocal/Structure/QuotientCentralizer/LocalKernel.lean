module

public import CFSG.Quasithin.Chapter15.Section03.Nonabelian.Fusion.Cubic.MLocal.Structure.QuotientCentralizer.Reduction
public import Theory.GroupTheory.PCoreLocalSetup

/-!
# The local kernel and the placement of the plane cubic

The genuine Sylow clauses of 15.3.59 and the earlier product I = YU give
[M : I] = 2. Indeed T normalizes the literal closure U because T lies in
H = C_G(Z). Together with Y normal in M and M = YT, this makes I normal
in M. The actual Sylow subgroup of I with ambient image T_K identifies
T ∩ I with T_K, and the normal-subgroup index formula finishes the step.

The quotient M/Y is a two-group. Since C_Y(V) = O₂(Y), the action kernel
C_M(V) is therefore a two-group as well. The prescribed equivalence
between the actual image of I and the two plane actors gives image order
36, compared with 72 for the full actor. The equal indices force the full
kernel inside I. Its relative normality puts it in P = O₂(I), and the
center equality V = Z(P) gives the reverse containment. Finally the
selected plane cubic has order three, so its image in M/I is trivial.

The source specialization uses precisely T ≤ M, U ≤ T, relative
Y-normality in M, C_Y(V) = O₂(Y), I = YU, M = YT, V = Z(P), the actual
Sylow witness with image T_K, [T : T_K] = 2, and the factors equivalence
of the genuine NaturalQuotientPair. It retains the source choice of g;
the earlier product and center conclusions have already used that choice.
The remaining constituent data of NaturalQuotientPair is retained for the
parent's centralizer calculation. The kernel argument also derives the
prime-to-three condition needed by card_planeCubic.

No ambient normality is imposed. Neither the order-nine quotient of Y,
the extraspecial description of U, nor U = Q_H is needed again in this
local deduction. The literal two-core P and two-residual in T_K are kept.
This proves the local branch from the stated genuine earlier inputs;
construction of those inputs and the remaining centralizer branches
belong to the source assembly owner.

Source: Aschbacher–Smith, combined manuscript (1 March 2004),
15.3.49(3–4), 15.3.53–55, 15.3.58(2), 15.3.59, and the setup of
15.3.60, printed pp.1142, 1146–1150.
-/

public section

open Subgroup
namespace CFSG.Quasithin.Chapter15.Section03.Nonabelian.Fusion.Cubic.MLocal.Structure.LocalKernel
variable {G : Type*} [Group G]

/-- The source Sylow index transports to I inside M, and I is normal there.
The Sylow premise is an actual Sylow subgroup with the prescribed ambient image. -/
theorem pairI_index_and_normalizer (T : Sylow 2 G) {M Y Z ZS : Subgroup G} {g : G}
    (hTM : (T : Subgroup G) ≤ M) (hTH : (T : Subgroup G) ≤ centralizerH Z)
    (hMY : M ≤ normalizer (Y : Set G))
    (hI : pairI Z ZS g = Y ⊔ closureU Z ZS)
    (hM : M = Y ⊔ (T : Subgroup G))
    (hIM : pairI Z ZS g ≤ M)
    (S : Sylow 2 (pairI Z ZS g))
    (hS : (S : Subgroup (pairI Z ZS g)).map (pairI Z ZS g).subtype =
      residualSylow T Z)
    (hidx : (residualSylow T Z).relIndex T = 2) :
    (pairI Z ZS g).relIndex M = 2 ∧
      M ≤ normalizer (pairI Z ZS g : Set G) := by
  let I := pairI Z ZS g
  have hYI : Y ≤ I := by
    change Y ≤ pairI Z ZS g
    rw [hI]
    exact le_sup_left
  have hTI : (T : Subgroup G) ≤ normalizer (I : Set G) := by
    change (T : Subgroup G) ≤ normalizer (pairI Z ZS g : Set G)
    rw [hI]
    exact (le_inf (hTM.trans hMY) (hTH.trans (H_normalizes_closureU Z ZS))).trans
      (normalizer_inf_normalizer_le_normalizer_sup Y (closureU Z ZS))
  have hn : M ≤ normalizer (I : Set G) := by
    rw [hM]
    exact sup_le (hYI.trans I.le_normalizer) hTI
  have hsup : I ⊔ (T : Subgroup G) = M :=
    le_antisymm (sup_le hIM hTM) (hM ▸ sup_le (hYI.trans le_sup_left) le_sup_right)
  have hi : (T : Subgroup G) ⊓ I = residualSylow T Z := by
    rw [← hS]
    exact inf_eq_sylow_map S T.isPGroup' (hS ▸ (show residualSylow T Z ≤ T from inf_le_left))
  let : (I.subgroupOf M).Normal := normal_subgroupOf_of_le_normalizer hn
  have he := relIndex_sup_left ((T : Subgroup G).subgroupOf M) (I.subgroupOf M)
  rw [← subgroupOf_sup hIM hTM, hsup, relIndex_subgroupOf le_rfl,
    relIndex_subgroupOf hTM] at he
  have he' : I.relIndex M = 2 := by
    rw [he, ← inf_relIndex_right, inf_comm, hi, hidx]
  exact ⟨he', hn⟩

private theorem quotient_two (N R : Subgroup G) [N.Normal]
    (hR : IsPGroup 2 R) (hs : N ⊔ R = ⊤) : IsPGroup 2 (G ⧸ N) := by
  let q := QuotientGroup.mk' N
  have hN : N.map q = ⊥ := by
    apply (Subgroup.map_eq_bot_iff _).mpr
    rw [QuotientGroup.ker_mk']
  have hr : R.map q = ⊤ := by
    have he := congrArg (Subgroup.map q) hs
    rw [Subgroup.map_sup, hN, bot_sup_eq,
      map_top_of_surjective q (QuotientGroup.mk'_surjective N)] at he
    exact he
  have hp : IsPGroup 2 (⊤ : Subgroup (G ⧸ N)) := hr ▸ hR.map q
  exact hp.of_equiv Subgroup.topEquiv

/-- A Sylow two-supplement and C_Y(V) = O₂(Y) make the full action kernel
a two-group. Normality is needed only for Y inside M. -/
theorem action_kernel_isTwoGroup (T : Sylow 2 G) {M Y V : Subgroup G}
    (hTM : (T : Subgroup G) ≤ M) (hYM : Y ≤ M)
    (hMY : M ≤ normalizer (Y : Set G))
    (hM : M = Y ⊔ (T : Subgroup G))
    (hCY : Y ⊓ centralizer (V : Set G) = Stellmacher.twoCoreAmbient Y)
    (d : NaturalOrthogonalAction M V) : IsPGroup 2 d.actor.ker := by
  let : (Y.subgroupOf M).Normal := normal_subgroupOf_of_le_normalizer hMY
  have hs : Y.subgroupOf M ⊔ (T : Subgroup G).subgroupOf M = ⊤ := by
    rw [← subgroupOf_sup hYM hTM, ← hM, subgroupOf_self]
  have hq := quotient_two (Y.subgroupOf M) ((T : Subgroup G).subgroupOf M)
    T.isPGroup'.comap_subtype hs
  let q := QuotientGroup.mk' (Y.subgroupOf M)
  intro a
  obtain ⟨n, hn⟩ := hq (q a.val)
  have hy : ((a.val : G) ^ 2 ^ n) ∈ Y := by
    change a.val ^ 2 ^ n ∈ Y.subgroupOf M
    apply (QuotientGroup.eq_one_iff (a.val ^ 2 ^ n)).mp
    change q (a.val ^ 2 ^ n) = 1
    rw [map_pow]
    exact hn
  have hc : ((a.val : G) ^ 2 ^ n) ∈ centralizer (V : Set G) := by
    have ha := a.property
    simp only [d.ker_actor] at ha
    exact pow_mem ha _
  have hp : ((a.val : G) ^ 2 ^ n) ∈ Stellmacher.twoCoreAmbient Y := hCY ▸ ⟨hy, hc⟩
  obtain ⟨m, hm⟩ := (show IsPGroup 2 (Stellmacher.twoCoreAmbient Y) from
    pCore_isPGroup.map Y.subtype) ⟨_, hp⟩
  refine ⟨n + m, ?_⟩
  apply Subtype.ext
  apply Subtype.ext
  have he := congrArg (fun x : Stellmacher.twoCoreAmbient Y => (x : G)) hm
  simpa only [coe_pow, coe_one, pow_add, pow_mul] using he

private theorem actor_card : Nat.card OrthogonalActor = 72 := by
  have hs : Nat.card OrthogonalPlaneActor = 6 := by
    rw [Nat.card_eq_fintype_card]
    decide +kernel
  rw [RegularWreathProduct.card, hs]
  norm_num [OrthogonalPlaneIndex, Nat.card_eq_fintype_card]

/-- The actual factor equivalence and the index in M force the whole
centralizer kernel into I. No identification of I with a tagged model is used. -/
theorem action_kernel_le_of_index_two {M V I : Subgroup G}
    (d : NaturalOrthogonalAction M V)
    (hidx : I.relIndex M = 2)
    (e : d.image I ≃* OrthogonalPlaneActor × OrthogonalPlaneActor) :
    M ⊓ centralizer (V : Set G) ≤ I := by
  have hc : Nat.card (d.image I) = 36 := by
    rw [Nat.card_congr e.toEquiv, Nat.card_prod]
    have hs : Nat.card OrthogonalPlaneActor = 6 := by
      rw [Nat.card_eq_fintype_card]
      decide +kernel
    rw [hs]
  have hi : (d.image I).index = 2 := by
    have h := (d.image I).card_mul_index
    rw [hc, actor_card] at h
    omega
  have hsup : (I.subgroupOf M ⊔ d.actor.ker).index = 2 := by
    rw [NaturalOrthogonalAction.image, Subgroup.index_map,
      MonoidHom.range_eq_top.mpr d.onto, index_top, mul_one] at hi
    exact hi
  have hrel := relIndex_mul_index
    (show I.subgroupOf M ≤ I.subgroupOf M ⊔ d.actor.ker from le_sup_left)
  change _ * _ = I.relIndex M at hrel
  rw [hsup, hidx] at hrel
  have he := relIndex_eq_one.mp (show
    (I.subgroupOf M).relIndex (I.subgroupOf M ⊔ d.actor.ker) = 1 by omega)
  have hk : d.actor.ker ≤ I.subgroupOf M := le_sup_right.trans he
  intro x hx
  exact hk (show (⟨x, hx.1⟩ : M) ∈ d.actor.ker by rw [d.ker_actor]; exact hx.2)

/-- Relative normality and the two-group property identify the local
kernel with the literal two-core, using V = Z(O₂(I)) for the reverse inclusion. -/
theorem centralizer_eq_twoCore_of_index_two {M V I : Subgroup G}
    (d : NaturalOrthogonalAction M V) (hIM : I ≤ M)
    (hidx : I.relIndex M = 2)
    (e : d.image I ≃* OrthogonalPlaneActor × OrthogonalPlaneActor)
    (hp : IsPGroup 2 d.actor.ker)
    (hcenter : V = (center (Stellmacher.twoCoreAmbient I)).map
      (Stellmacher.twoCoreAmbient I).subtype) :
    M ⊓ centralizer (V : Set G) = Stellmacher.twoCoreAmbient I := by
  have hCI := action_kernel_le_of_index_two d hidx e
  let f := d.actor.comp (inclusion hIM)
  have hf : f.ker.map I.subtype = M ⊓ centralizer (V : Set G) := by
    ext x
    constructor
    · rintro ⟨a, ha, rfl⟩
      refine ⟨hIM a.property, ?_⟩
      have hk : inclusion hIM a ∈ d.actor.ker := ha
      rw [d.ker_actor] at hk
      exact hk
    · intro hx
      refine ⟨⟨x, hCI hx⟩, ?_, rfl⟩
      change (⟨x, hIM (hCI hx)⟩ : M) ∈ d.actor.ker
      rw [d.ker_actor]
      exact hx.2
  have hfp : IsPGroup 2 f.ker := hp.comap_of_injective (inclusion hIM)
    (inclusion_injective hIM)
  have hcore : f.ker ≤ pCore 2 I := le_sSup ⟨inferInstance, hfp⟩
  apply le_antisymm
  · rw [← hf]
    exact map_mono hcore
  · exact le_inf ((map_subtype_le _).trans hIM) (le_centralizer_lower_of_center hcenter)

/-- An order-three subgroup of M lies in every relatively normal subgroup
of index two. The index and cardinality are taken in the actual local groups. -/
theorem cubic_le_of_index_two {M I D : Subgroup G}
    (hDM : D ≤ M) (hn : M ≤ normalizer (I : Set G))
    (hidx : I.relIndex M = 2) (hcard : Nat.card D = 3) : D ≤ I := by
  let : (I.subgroupOf M).Normal := normal_subgroupOf_of_le_normalizer hn
  have h2 : (I.subgroupOf M).relIndex (D.subgroupOf M) ∣ 2 :=
    hidx ▸ relIndex_dvd_index_of_normal (I.subgroupOf M) (D.subgroupOf M)
  have h3 : (I.subgroupOf M).relIndex (D.subgroupOf M) ∣ 3 := by
    have hd := relIndex_dvd_card (I.subgroupOf M) (D.subgroupOf M)
    rwa [Nat.card_congr (subgroupOfEquivOfLe hDM).toEquiv, hcard] at hd
  have hle := relIndex_eq_one.mp (Nat.eq_one_of_dvd_coprimes
    (by decide : Nat.Coprime 2 3) h2 h3)
  exact fun x hx => hle (show (⟨x, hDM hx⟩ : M) ∈ D.subgroupOf M from hx)

/-- The local branch in the setup of 15.3.60: [M : I] = 2, C_M(V) = P,
and the selected plane cubic lies in I. All displayed groups have their
literal source definitions, and the quotient normalization is constructed
from the center equality and the definition of P. -/
theorem source_local_kernel [Finite G] (T : Sylow 2 G) (M : Subgroup G)
    (hTM : (T : Subgroup G) ≤ M) (d : NaturalOrthogonalAction M (localModule T M))
    (i : OrthogonalPlaneIndex) (g : G) :
    let Z := centralInvolutions T
    let V := localModule T M
    let H := centralizerH Z
    let Y := residualY M H
    let V1 := d.plane i
    let ZS := fixedPlane V (planeStabilizer T V1)
    let U := closureU Z ZS
    let I := pairI Z ZS g
    let P := pairP Z ZS g
    let TK := residualSylow T Z
    ∀ (_hg : g ∈ Y) (_hmoving : ¬ rightConjugate Z g ≤ V ⊓ U)
      (hUT : U ≤ T) (_hMY : M ≤ normalizer (Y : Set G))
      (_hCY : Y ⊓ centralizer (V : Set G) = Stellmacher.twoCoreAmbient Y)
      (hI : I = Y ⊔ U) (_hM : M = Y ⊔ (T : Subgroup G))
      (hcenter : V = (center P).map P.subtype)
      (S : Sylow 2 I) (_hS : (S : Subgroup I).map I.subtype = TK)
      (_hidx : TK.relIndex T = 2),
    let hIM : I ≤ M := hI.le.trans (sup_le (show Y ≤ M from map_subtype_le _) (hUT.trans hTM))
    letI := normal_lower_of_center hcenter
    ∀ (_r : NaturalQuotientPair d I P hIM (pairI_normalizes_pairP Z ZS g))
      (PM3 : Sylow 3 (M ⊓ centralizer (V1 : Set G) : Subgroup G)),
      I.relIndex M = 2 ∧ M ⊓ centralizer (V : Set G) = P ∧
        planeCubic M V1 PM3 ≤ I := by
  intro Z V H Y V1 ZS U I P TK _hg _hmoving hUT hMY hCY hI hM hcenter S hS hidx hIM r PM3
  let : (V.subgroupOf P).Normal := normal_lower_of_center hcenter
  have hTH : (T : Subgroup G) ≤ centralizerH Z := by
    intro t ht z hz
    exact (centralInvolutions_le_centralizer_sylow T hz t ht).symm
  obtain ⟨hindex, hnormal⟩ := pairI_index_and_normalizer T hTM hTH hMY hI hM hIM S hS hidx
  have hp := action_kernel_isTwoGroup T hTM (show Y ≤ M from map_subtype_le _) hMY hM hCY d
  have hc : M ⊓ centralizer (V : Set G) = P :=
    centralizer_eq_twoCore_of_index_two d hIM hindex r.factors hp hcenter
  have hcop : Nat.Coprime 3 (Nat.card ((centralizer (V : Set G)).subgroupOf M)) := by
    rw [← d.ker_actor]
    obtain ⟨n, hn⟩ := hp.exists_card_eq
    rw [hn]
    exact (by decide : Nat.Coprime 3 2).pow_right n
  exact ⟨hindex, hc, cubic_le_of_index_two (planeCubic_le_M M V1 PM3) hnormal hindex
    (card_planeCubic d hcop i PM3)⟩

end CFSG.Quasithin.Chapter15.Section03.Nonabelian.Fusion.Cubic.MLocal.Structure.LocalKernel
