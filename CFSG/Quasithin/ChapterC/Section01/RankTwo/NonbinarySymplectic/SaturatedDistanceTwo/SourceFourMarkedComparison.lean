module
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.SaturatedDistanceTwo.SourceFourRootSelection
public import Theory.Representation.SymplecticFourOrthogonalCover.SylowFlag.Stabilizers.Shears

/-!
# Marked hyperplane comparison and escape exclusion in source (4)

For a supplied full-cover plane marking, the fixed hyperplane and its literal
section centralizer determine each other. Reconstructing the earlier cover
geometry therefore recovers their index, direct complement and root movement
without choosing a different hyperplane.

In the escaping unequal-attachment branch, the two full attachments have
order q. The radical factorization gives the common displacement as the
product of the opposite hyperplane movement and its section-centralizer
complement, of orders q squared and q. The product order makes them disjoint.
The root movement has order q squared as well, so its intersection with the
opposite movement cannot be trivial inside the common group of order q cubed.
These facts discharge every additional premise of the marked root-selection
comparison. The complete attachment is exactly that intersection, by the
same direct-complement factorization.

For the symmetric comparison, the opposite centralizer has field index q.
Its displacement is a line in the plane radical; transitivity inside the
plane parabolic marks that line without changing the full covering action.
The resulting opposite marked hyperplane is exactly the original centralizer.
The two intersection identities would equate the unequal attachments, so
an escaping opposite centralizer is impossible.

The existential applications construct HasMarkedHyperplane from the actual
preceding plane cover. No attachment comparison is included in that predicate.
The nonescaping commutator-value argument of (4), source (5)/(6), and n = 2
with the block conclusion remain with the final assembly. The Chapter11
applications retain the original intrinsic quotient and action.

Source: Meierfrankenfeld--Stellmacher, *Pushing up weak BN-pairs of rank two*
(1993), (3.7)(4), printed p.875. The private central-supplement and complement
transports adapt SourceFourComplement at the supplied marked hyperplane.
-/

public noncomputable section
open Subgroup Representation Representation.OneCohomology
open Representation.SymplecticFourOrthogonalCover
open Theory.SpecificGroups.SymplecticFour
open scoped commutatorElement IsMulCommutative
open Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
namespace CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic.SaturatedDistanceTwo
open DistanceTwoRecognition ChapterB.QuasisimpleSource
variable {H F : Type*} [Group H] [Finite H] [Field F] [Finite F] [CharP F 2]
variable {K R : Subgroup H} {n : ℕ} (h : Input K R n F)
variable (d : CharacteristicReduction K R)
include h

omit [Group H] [Finite H] [Field F] [Finite F] [CharP F 2] h in
private theorem movement_central_supplement
    {G : Type*} [Group G] (U C Y A : Subgroup G)
    (hCU : C ≤ normalizer (U : Set G)) (hCY : C ≤ centralizer (Y : Set G))
    (hAY : A ≤ Y) : ⁅A,U ⊔ C⁆=⁅A,U⁆ := by
  apply le_antisymm ?_ (commutator_mono le_rfl le_sup_left)
  apply commutator_le.mpr
  intro b hb x hx
  rw [←SetLike.mem_coe,coe_mul_of_right_le_normalizer_left _ _ hCU] at hx
  obtain ⟨u,hu,c,hc,rfl⟩ := hx
  have hbc : Commute b c := hCY hc b (hAY hb)
  rw [commutatorElement_mul_right_eq_mul_conj,commutatorElement_eq_one_iff_commute.mpr hbc]
  simpa only [mul_one,mul_inv_cancel_right] using commutator_mem_commutator hb hu


private theorem marked_hyperplane_geometry
    (g : Geometry d.radical) (hb : g.b d.radical=2)
    (hsat : (normalizer (d.radical : Set d.overgroup)).pCoreIn 2=d.radical)
    {a z t : Vertex d.radical} (path : CriticalPath d.radical g a z)
    (hat : Adjacent d.radical a t) (hzt : Adjacent d.radical z t)
    (c : EdgeMarking h d a t) (c' : EdgeMarking h d z t)
    (hcritical : (2^n)^2 ≤ (Q d.radical z).relIndex (Z d.radical a))
    (P B : Subgroup (FreeAmalgam d.radical))
    (hmarked : HasMarkedHyperplane h d z t P B) :
    let X := Z d.radical z ⊓ centralizer (P : Set (FreeAmalgam d.radical))
    let H₀ := ⁅Z d.radical z,P⁆
    let A₀ := U d.radical z ⊓ centralizer (Ltilde d.radical z : Set (FreeAmalgam d.radical))
    Q d.radical z ≤ P ∧ P ≤ Q d.radical t ∧ B ≤ Q d.radical t ∧
      P=Q d.radical t ⊓ centralizer (X : Set (FreeAmalgam d.radical)) ∧
      X.relIndex (Z d.radical z)=2^n ∧
      Z d.radical t ≤ X ∧ ⁅Z d.radical a,Z d.radical z⁆ ≤ X ∧
      (∀ b : FreeAmalgam d.radical, b ∈ B ↔ b ∈ Q d.radical t ∧ ∀ x ∈ X, ⁅b,x⁆ ∈ H₀) ∧
      Disjoint ⁅X,B⁆ A₀ ∧ Nat.card (⁅X,B⁆ : Subgroup (FreeAmalgam d.radical))=2^n ∧
      H₀=⁅X,B⁆ ⊔ A₀ ∧ H₀ ≤ ⁅Z d.radical a,Z d.radical z⁆ ∧ B.relIndex (Q d.radical t)=2^n := by
  obtain ⟨cv,k,hk,hP,hB,hpoint,hfix,hmem⟩ := hmarked
  obtain ⟨P₀,B₀,hP₀,hB₀,hpoint₀,hindex,hfix₀,hmem₀,hdis,hcard,hjoin⟩ :=
    plane_cover_hyperplane_attachment h d cv k hk
  have hXeq : U d.radical z ⊓ centralizer (P₀ : Set (FreeAmalgam d.radical)) =
      U d.radical z ⊓ centralizer (P : Set (FreeAmalgam d.radical)) := by
    ext x
    constructor
    · rintro ⟨hx,hc⟩
      refine ⟨hx,?_⟩
      obtain ⟨w,rfl⟩ := cv.range_eq.symm ▸ hx
      exact (hfix w.toAdd).mpr ((hfix₀ w.toAdd).mp hc)
    · rintro ⟨hx,hc⟩
      refine ⟨hx,?_⟩
      obtain ⟨w,rfl⟩ := cv.range_eq.symm ▸ hx
      exact (hfix₀ w.toAdd).mpr ((hfix w.toAdd).mp hc)
  have hPeq : P₀=P := hpoint₀.trans ((congrArg
    (fun S : Subgroup (FreeAmalgam d.radical) => Q d.radical t ⊓ centralizer (S : Set (FreeAmalgam d.radical))) hXeq).trans hpoint.symm)
  subst P₀
  have hBeq : B₀=B := by
    ext b
    exact (hmem₀ b).trans (hmem b).symm
  subst B₀
  have hBi := plane_cover_hyperplane_section_index h d cv k hk P B hP hpoint hfix hmem
  let C := Z d.radical t
  let V := U d.radical z
  let X₀ := V ⊓ centralizer (P : Set (FreeAmalgam d.radical))
  let X₁ := Z d.radical z ⊓ centralizer (P : Set (FreeAmalgam d.radical))
  let Y := Q d.radical t
  have hgen : Z d.radical z=V ⊔ C :=
    Z_eq_moving_sup_edge_of_distance_two h d g hb path.end_color hzt
  have ht : color d.radical t=true := by
    apply Bool.eq_true_of_not_eq_false
    intro he
    exact adjacent_color_ne d.radical hzt (path.end_color.trans he.symm)
  have hC : C=omegaCenter Y := by simp [C,Y,Z,ht,edgeOmega]
  have hCY : C ≤ centralizer (Y : Set (FreeAmalgam d.radical)) := by
    rw [hC]
    exact fun x hx => (mem_omegaCenter_iff.mp hx).2.2
  let := g.Z_elementary (by omega : 0 < g.b d.radical) z path.end_color
  have hCZ : C ≤ Z d.radical z := Sp4Four.edge_Z_le_endpoint d.radical path.end_color hzt
  have hCU : C ≤ normalizer (V : Set (FreeAmalgam d.radical)) :=
    (hCZ.trans ((Z d.radical z).le_centralizer.trans (centralizer_le (U_le_Z z)))).trans
      (Subgroup.centralizer_le_normalizer _)
  have hCX : C ≤ normalizer (X₀ : Set (FreeAmalgam d.radical)) :=
    (hCZ.trans ((Z d.radical z).le_centralizer.trans
      (centralizer_le (inf_le_left.trans (U_le_Z z))))).trans
        (Subgroup.centralizer_le_normalizer _)
  have hCP : C ≤ centralizer (P : Set (FreeAmalgam d.radical)) := hCY.trans (centralizer_le hP)
  have hX : X₁=X₀ ⊔ C := by
    dsimp only [X₁,X₀]
    rw [hgen,sup_comm V C,inf_centralizer_sup_of_centralizing C V P hCU hCP,sup_comm]
  have hHZ : ⁅Z d.radical z,P⁆=⁅P,V⁆ := by
    rw [commutator_comm,hgen]
    exact movement_central_supplement V C Y P hCU hCY hP
  have hXB : ⁅X₁,B⁆=⁅X₀,B⁆ := by
    rw [commutator_comm _ B,hX,movement_central_supplement X₀ C Y B hCX hCY hB,
      commutator_comm]
  have hpointZ : P=Y ⊓ centralizer (X₁ : Set (FreeAmalgam d.radical)) := by
    apply le_antisymm
    · refine le_inf hP ?_
      rw [hX]
      apply le_centralizer_iff.mpr
      exact sup_le (le_centralizer_iff.mp (hpoint.le.trans inf_le_right)) hCP
    · exact (inf_le_inf_left Y (centralizer_le
        (show X₀ ≤ X₁ from hX ▸ le_sup_left))).trans hpoint.ge
  have hQ : Q d.radical z ≤ P := by
    rw [hpointZ]
    apply le_inf c'.core_le_edge
    exact le_centralizer_iff.mp
      (inf_le_left.trans (commutator_eq_bot_iff_le_centralizer.mp
        (Z_centralizes_Q d.radical z path.end_color)))
  have hi : X₁.relIndex (Z d.radical z)=2^n := by
    let := finite_Z d.radical z
    let : Finite X₁ := Finite.of_injective (inclusion (show X₁ ≤ Z d.radical z from inf_le_left))
      (inclusion_injective _)
    have hVX : V ⊔ X₁=Z d.radical z := by
      rw [hX,←sup_assoc,sup_eq_left.mpr (show X₀ ≤ V from inf_le_left),←hgen]
    have hXU : X₁ ≤ normalizer (V : Set (FreeAmalgam d.radical)) :=
      (inf_le_left.trans ((Z d.radical z).le_centralizer.trans (centralizer_le (U_le_Z z)))).trans
        (Subgroup.centralizer_le_normalizer _)
    rw [←hVX,relIndex_sup_of_normalizes V X₁ hXU]
    have hInf : X₁ ⊓ V=X₀ := by
      ext x
      exact ⟨fun hx => ⟨hx.2,hx.1.2⟩,fun hx => ⟨⟨U_le_Z z hx.1,hx.2⟩,hx.1⟩⟩
    rw [←inf_relIndex_right,hInf,inf_relIndex_left]
    exact hindex
  have hCX₁ : C ≤ X₁ := le_inf hCZ hCP
  have hZaQ : Z d.radical a ≤ Q d.radical a :=
    (g.omega_bound a path.start_color (by
      rw [g.distance_constant a path.start_color]; change 0 < g.b d.radical; omega)).trans
      (omegaCenter_le _)
  have hcommon : ⁅Z d.radical a,Z d.radical z⁆ ≤ C := by
    rw [commutator_comm]
    exact (commutator_mono le_rfl hZaQ).trans
      (source_two_midpoint_containment h d g hb hsat path hat hzt c c')
  refine ⟨hQ,hP,hB,hpointZ,hi,hCX₁,hcommon.trans hCX₁,?_,?_,?_,?_,?_,hBi⟩
  · intro b
    rw [hmem]
    constructor
    · rintro ⟨hb,hm⟩
      refine ⟨hb,fun x hx => ?_⟩
      change x ∈ X₁ at hx
      rw [hX,←SetLike.mem_coe,coe_mul_of_right_le_normalizer_left _ _ hCX] at hx
      obtain ⟨u,hu,v,hv,rfl⟩ := hx
      have hbv : Commute b v := hCY hv b hb
      rw [hHZ,commutatorElement_mul_right_eq_mul_conj,
        commutatorElement_eq_one_iff_commute.mpr hbv]
      simpa only [mul_one,mul_inv_cancel_right] using hm u hu
    · rintro ⟨hb,hm⟩
      refine ⟨hb,fun x hx => ?_⟩
      rw [←hHZ]
      apply hm x
      change x ∈ X₁
      rw [hX]
      exact mem_sup_left hx
  · rw [hXB]
    exact hdis
  · rw [hXB]
    exact hcard
  · rw [hHZ,hXB]
    exact hjoin
  · rw [commutator_comm]
    exact (commutator_mono hP le_rfl).trans_eq
      (source_four_large_full_movement h d g hb hsat path hat hzt c c' hcritical)

omit [Group H] [Finite H] [Field F] [Finite F] [CharP F 2] h in
private theorem subgroup_product_card {G : Type*} [Group G]
    (B C : Subgroup G) (hn : C ≤ normalizer (B : Set G)) :
    Nat.card B * Nat.card C = Nat.card (B ⊓ C : Subgroup G) * Nat.card (B ⊔ C : Subgroup G) := by
  let V := B ⊔ C
  let _ : (B.subgroupOf V).Normal :=
    normal_subgroupOf_of_le_normalizer (sup_le B.le_normalizer hn)
  have hindex := relIndex_sup_left (C.subgroupOf V) (B.subgroupOf V)
  rw [← subgroupOf_sup le_sup_left le_sup_right,
    relIndex_subgroupOf le_rfl,relIndex_subgroupOf le_sup_right] at hindex
  have hindex' : B.relIndex V = (B ⊓ C).relIndex C :=
    hindex.trans (inf_relIndex_right B C).symm
  have hcardV := relIndex_mul_relIndex (⊥ : Subgroup G) B V bot_le le_sup_left
  have hcardC := relIndex_mul_relIndex (⊥ : Subgroup G) (B ⊓ C) C bot_le inf_le_right
  simp only [relIndex_bot_left] at hcardV hcardC
  rw [hindex'] at hcardV
  rw [←hcardC,←hcardV]
  ac_rfl

private theorem marked_escaping_intersection
    (g : Geometry d.radical) (hb : g.b d.radical=2)
    (hsat : (normalizer (d.radical : Set d.overgroup)).pCoreIn 2=d.radical)
    {a z t : Vertex d.radical} (path : CriticalPath d.radical g a z)
    (hat : Adjacent d.radical a t) (hzt : Adjacent d.radical z t)
    (c : EdgeMarking h d a t) (c' : EdgeMarking h d z t)
    (hcritical : (2^n)^2 ≤ (Q d.radical z).relIndex (Z d.radical a))
    (P B : Subgroup (FreeAmalgam d.radical))
    (hmarked : HasMarkedHyperplane h d z t P B)
    (hP : P ≤ Q d.radical t) (hB : B ≤ Q d.radical t)
    (hpoint : P=Q d.radical t ⊓ centralizer
      (Z d.radical z ⊓ centralizer (P : Set (FreeAmalgam d.radical)) : Set (FreeAmalgam d.radical)))
    (hi : (Z d.radical z ⊓ centralizer (P : Set (FreeAmalgam d.radical))).relIndex (Z d.radical z)=2^n)
    (hmem : ∀ b : FreeAmalgam d.radical, b ∈ B ↔ b ∈ Q d.radical t ∧
      ∀ x ∈ Z d.radical z ⊓ centralizer (P : Set (FreeAmalgam d.radical)), ⁅b,x⁆ ∈ ⁅Z d.radical z,P⁆)
    (hdis : Disjoint ⁅Z d.radical z ⊓ centralizer (P : Set (FreeAmalgam d.radical)),B⁆
      (U d.radical z ⊓ centralizer (Ltilde d.radical z : Set (FreeAmalgam d.radical))))
    (hcard : Nat.card (⁅Z d.radical z ⊓ centralizer (P : Set (FreeAmalgam d.radical)),B⁆ :
      Subgroup (FreeAmalgam d.radical))=2^n)
    (hjoin : ⁅Z d.radical z,P⁆ = ⁅Z d.radical z ⊓ centralizer (P : Set (FreeAmalgam d.radical)),B⁆ ⊔
      (U d.radical z ⊓ centralizer (Ltilde d.radical z : Set (FreeAmalgam d.radical))))
    (hR : ⁅Z d.radical z,P⁆ ≤ ⁅Z d.radical a,Z d.radical z⁆)
    (hBi : B.relIndex (Q d.radical t)=2^n)
    (hne : U d.radical a ⊓ centralizer (Ltilde d.radical a : Set (FreeAmalgam d.radical)) ≠
      U d.radical z ⊓ centralizer (Ltilde d.radical z : Set (FreeAmalgam d.radical)))
    (hescape : ¬ Z d.radical a ⊓ centralizer
      (Z d.radical z ⊓ centralizer (P : Set (FreeAmalgam d.radical)) : Set (FreeAmalgam d.radical)) ≤ Q d.radical z) :
    U d.radical z ⊓ centralizer (Ltilde d.radical z : Set (FreeAmalgam d.radical)) =
      ⁅Z d.radical z ⊓ centralizer (P : Set (FreeAmalgam d.radical)),Z d.radical a⁆ ⊓
        ⁅Z d.radical z,P⁆ := by
  let X := Z d.radical z ⊓ centralizer (P : Set (FreeAmalgam d.radical))
  let D := ⁅Z d.radical a,Z d.radical z⁆
  let M := ⁅X,Z d.radical a⁆
  let A := ⁅X,B⁆
  have hfull : Nat.card (U d.radical a ⊓ centralizer (Ltilde d.radical a : Set (FreeAmalgam d.radical)) :
      Subgroup (FreeAmalgam d.radical))=2^n := by
    by_contra hn
    exact hne (source_four_large_escaping_small_attachment_eq h d g hb hsat path hat hzt c c'
      hcritical P hP hpoint hi hescape hn)
  have hfull' := (source_four_large_attachment_card_eq h d g hb hsat path hat hzt c c' hcritical).symm.trans hfull
  have hn := source_four_large_escaping_not_le_hyperplane h d g hb hsat path hat hzt c c'
    hcritical P B hP hpoint hi hmem hcard hne hescape
  have hZaT : Z d.radical a ≤ Q d.radical t :=
    (g.omega_bound a path.start_color (by
      rw [g.distance_constant a path.start_color]; change 0 < g.b d.radical; omega)).trans
      ((omegaCenter_le _).trans c.core_le_edge)
  have he : Z d.radical a ⊓ B=Z d.radical a ⊓ centralizer (X : Set (FreeAmalgam d.radical)) := by
    apply le_antisymm
    · rintro u ⟨hu,hbB⟩
      refine ⟨hu,?_⟩
      apply (source_four_large_full_section_centralizer h d g hb hsat path hat hzt c c'
        hcritical P hP hpoint hi hescape hfull hn u hu).mp
      intro x hx
      rw [←commutatorElement_inv]
      exact inv_mem (((hmem u).mp hbB).2 x hx)
    · rintro u ⟨hu,hc⟩
      refine ⟨hu,(hmem u).mpr ⟨hZaT hu,?_⟩⟩
      intro x hx
      rw [commutatorElement_eq_one_iff_commute.mpr (hc x hx).symm]
      exact one_mem _
  have hBZ : B.relIndex (Z d.radical a)=2^n := by
    rw [←inf_relIndex_left,he]
    exact (source_four_large_escaping_hyperplane h d g hb hsat path hat hzt c c'
      hcritical P hP hpoint hi hescape).1
  let := finite_stabilizer d.radical z
  let : Finite (Q d.radical t) := Finite.of_injective
    (inclusion c'.edge_le) (inclusion_injective _)
  let : Finite B := Finite.of_injective (inclusion hB) (inclusion_injective _)
  have hnorm : B ≤ normalizer (Z d.radical a : Set (FreeAmalgam d.radical)) :=
    hB.trans (c.edge_le.trans (Z_normalized d.radical a))
  have hJ : Z d.radical a ⊔ B ≤ Q d.radical t := sup_le hZaT hB
  have hfactor : Q d.radical t=Z d.radical a ⊔ B := by
    have hh := relIndex_mul_relIndex B (Z d.radical a ⊔ B) (Q d.radical t) le_sup_right hJ
    rw [relIndex_sup_of_normalizes _ _ hnorm,hBZ,hBi] at hh
    have hidx : (Z d.radical a ⊔ B).relIndex (Q d.radical t)=1 := by
      exact Nat.eq_of_mul_eq_mul_left (by positivity : 0 < 2^n) (hh.trans (mul_one _).symm)
    exact le_antisymm (relIndex_eq_one.mp hidx) hJ
  have hXD : ⁅X,Q d.radical t⁆=D :=
    source_four_large_hyperplane_full_movement h d g hb hsat path hat hzt c c' hcritical P hP hi
  have hMD : M ≤ D := (commutator_mono le_rfl hZaT).trans_eq hXD
  have hAD : A ≤ D := (commutator_mono le_rfl hB).trans_eq hXD
  have hDC : D ≤ Z d.radical t := by
    change ⁅Z d.radical a,Z d.radical z⁆ ≤ Z d.radical t
    rw [commutator_comm]
    exact (commutator_mono le_rfl ((g.omega_bound a path.start_color (by
      rw [g.distance_constant a path.start_color]; change 0 < g.b d.radical; omega)).trans
      (omegaCenter_le _))).trans (source_two_midpoint_containment h d g hb hsat path hat hzt c c')
  have ht : color d.radical t=true := by
    apply Bool.eq_true_of_not_eq_false
    intro hh
    exact adjacent_color_ne d.radical hzt (path.end_color.trans hh.symm)
  have hDT : D ≤ centralizer (Q d.radical t : Set (FreeAmalgam d.radical)) := by
    apply hDC.trans
    rw [show Z d.radical t=omegaCenter (Q d.radical t) by simp [Z,ht,edgeOmega]]
    exact fun x hx => (mem_omegaCenter_iff.mp hx).2.2
  have hsup : D=M ⊔ A := by
    apply le_antisymm ?_ (sup_le hMD hAD)
    rw [←hXD]
    apply commutator_le.mpr
    intro x hx b hbT
    rw [hfactor,←SetLike.mem_coe,coe_mul_of_right_le_normalizer_left _ _ hnorm] at hbT
    obtain ⟨u,hu,v,hv,rfl⟩ := hbT
    have hxv : ⁅x,v⁆ ∈ A := commutator_mem_commutator hx hv
    have hh := hDT (hAD hxv) u (hZaT hu)
    rw [commutatorElement_mul_right_eq_mul_conj,mul_assoc ⁅x,u⁆ u ⁅x,v⁆,hh,
      ←mul_assoc ⁅x,u⁆ ⁅x,v⁆ u,mul_inv_cancel_right]
    exact (M ⊔ A).mul_mem (mem_sup_left (commutator_mem_commutator hx hu)) (mem_sup_right hxv)
  have hMc : Nat.card M=(2^n)^2 := by
    have hh := (source_four_large_escaping_movement h d g hb hsat path hat hzt c c'
      hcritical P hP hpoint hi hescape).2.2
    simpa only [hfull,pow_two] using hh
  have hDc : Nat.card D=(2^n)^3 := by
    rw [(source_four_large_displacement_order h d g hb hsat path hat hzt c c' hcritical).2.2,hfull']
    exact (pow_succ (2^n) 2).symm
  have hDA : Disjoint M A := by
    have hDZ : D ≤ Z d.radical z := hDC.trans (Sp4Four.edge_Z_le_endpoint d.radical path.end_color hzt)
    let := g.Z_elementary (by omega : 0 < g.b d.radical) z path.end_color
    have hAM : A ≤ normalizer (M : Set (FreeAmalgam d.radical)) :=
      (hAD.trans hDZ).trans ((Z d.radical z).le_centralizer.trans (centralizer_le (hMD.trans hDZ)))
        |>.trans (Subgroup.centralizer_le_normalizer _)
    have hh := subgroup_product_card M A hAM
    rw [hMc,hcard,←hsup,hDc,←pow_succ] at hh
    apply disjoint_iff.mpr
    apply Subgroup.card_eq_one.mp
    apply Nat.eq_of_mul_eq_mul_right (by positivity : 0 < (2^n)^3)
    simpa only [one_mul] using hh.symm
  let A₀ := U d.radical z ⊓ centralizer (Ltilde d.radical z : Set (FreeAmalgam d.radical))
  let N := ⁅Z d.radical z,P⁆
  have hDZ : D ≤ Z d.radical z := hDC.trans
    (Sp4Four.edge_Z_le_endpoint d.radical path.end_color hzt)
  let := g.Z_elementary (by omega : 0 < g.b d.radical) z path.end_color
  have hA₀A : A₀ ≤ normalizer (A : Set (FreeAmalgam d.radical)) :=
    (inf_le_left.trans (U_le_Z z)).trans
      ((Z d.radical z).le_centralizer.trans (centralizer_le (hAD.trans hDZ))) |>.trans
        (Subgroup.centralizer_le_normalizer _)
  have hNc : Nat.card N=(2^n)^2 := by
    change Nat.card (⁅Z d.radical z,P⁆ : Subgroup (FreeAmalgam d.radical))=_
    rw [hjoin,card_sup_eq_mul_of_normalizes_of_disjoint _ _ hA₀A hdis,hcard,hfull',pow_two]
  have hNM : N ≤ normalizer (M : Set (FreeAmalgam d.radical)) :=
    (hR.trans hDZ).trans ((Z d.radical z).le_centralizer.trans (centralizer_le (hMD.trans hDZ)))
      |>.trans (Subgroup.centralizer_le_normalizer _)
  let : Finite D := Nat.finite_of_card_ne_zero (by rw [hDc]; positivity)
  have hmeet : (M ⊓ N : Subgroup (FreeAmalgam d.radical)) ≠ ⊥ := by
    intro hbot
    have hp := subgroup_product_card M N hNM
    rw [hMc,hNc,hbot,Subgroup.card_bot,one_mul] at hp
    have hc := Nat.card_le_card_of_injective (inclusion (sup_le hMD hR)) (inclusion_injective _)
    rw [hDc,←hp] at hc
    have hq : 1 < 2^n := one_lt_pow₀ (by decide : 1 < (2:ℕ)) (by have := h.nonbinary; omega)
    have hlt : (2^n)^3 < (2^n)^2*(2^n)^2 := by
      calc
        (2^n)^3 < (2^n)^4 := Nat.pow_lt_pow_right hq (by decide)
        _ = (2^n)^2*(2^n)^2 := by ring
    exact hlt.not_ge hc
  have hle : A₀ ≤ M := source_four_large_marked_attachment_le h d g hb hsat
    path hat hzt c c' hcritical P B hmarked hi hescape hfull hNc hn hmeet hDA
  apply le_antisymm (le_inf hle (hjoin ▸ le_sup_right))
  rintro x ⟨hxM,hxN⟩
  change x ∈ ⁅Z d.radical z,P⁆ at hxN
  rw [hjoin,←SetLike.mem_coe,coe_mul_of_right_le_normalizer_left _ _ hA₀A] at hxN
  obtain ⟨b,hbA,a₀,ha₀,rfl⟩ := hxN
  have hbM : b ∈ M := by
    simpa only [mul_inv_cancel_right] using M.mul_mem hxM (M.inv_mem (hle ha₀))
  have hb1 : b=1 := hDA.le_bot ⟨hbM,hbA⟩
  change b*a₀ ∈ A₀
  rw [hb1,one_mul]
  exact ha₀

/-- For the same marked hyperplane supplied by the full plane cover, all
order, intersection and complement premises of root selection are consequences
of the original source geometry. In the escaping unequal-attachment branch,
the entire attachment is exactly the intersection of the two movements. -/
theorem source_four_large_marked_attachment_intersection
    (g : Geometry d.radical) (hb : g.b d.radical=2)
    (hsat : (normalizer (d.radical : Set d.overgroup)).pCoreIn 2=d.radical)
    {a z t : Vertex d.radical} (path : CriticalPath d.radical g a z)
    (hat : Adjacent d.radical a t) (hzt : Adjacent d.radical z t)
    (c : EdgeMarking h d a t) (c' : EdgeMarking h d z t)
    (hcritical : (2^n)^2 ≤ (Q d.radical z).relIndex (Z d.radical a))
    (hne : U d.radical a ⊓ centralizer (Ltilde d.radical a : Set (FreeAmalgam d.radical)) ≠
      U d.radical z ⊓ centralizer (Ltilde d.radical z : Set (FreeAmalgam d.radical)))
    (P B : Subgroup (FreeAmalgam d.radical))
    (hmarked : HasMarkedHyperplane h d z t P B)
    (hescape : ¬ Z d.radical a ⊓ centralizer
      (Z d.radical z ⊓ centralizer (P : Set (FreeAmalgam d.radical)) : Set (FreeAmalgam d.radical)) ≤ Q d.radical z) :
    U d.radical z ⊓ centralizer (Ltilde d.radical z : Set (FreeAmalgam d.radical)) =
      ⁅Z d.radical z ⊓ centralizer (P : Set (FreeAmalgam d.radical)),Z d.radical a⁆ ⊓
        ⁅Z d.radical z,P⁆ := by
  obtain ⟨hQ,hP,hB,hpoint,hi,hCX,hRX,hmem,hdis,hcard,hjoin,hR,hBi⟩ :=
    marked_hyperplane_geometry h d g hb hsat path hat hzt c c' hcritical P B hmarked
  exact marked_escaping_intersection h d g hb hsat path hat hzt c c' hcritical
    P B hmarked hP hB hpoint hi hmem hdis hcard hjoin hR hBi hne hescape

/-- The preceding plane geometry constructs the marked source hyperplane;
no comparison or intersection hypothesis is included in that construction. -/
theorem source_four_large_unequal_marked_intersection
    (g : Geometry d.radical) (hb : g.b d.radical=2)
    (hsat : (normalizer (d.radical : Set d.overgroup)).pCoreIn 2=d.radical)
    {a z t : Vertex d.radical} (path : CriticalPath d.radical g a z)
    (hat : Adjacent d.radical a t) (hzt : Adjacent d.radical z t)
    (c : EdgeMarking h d a t) (c' : EdgeMarking h d z t)
    (hcritical : (2^n)^2 ≤ (Q d.radical z).relIndex (Z d.radical a))
    (hne : U d.radical a ⊓ centralizer (Ltilde d.radical a : Set (FreeAmalgam d.radical)) ≠
      U d.radical z ⊓ centralizer (Ltilde d.radical z : Set (FreeAmalgam d.radical))) :
    ∃ P B : Subgroup (FreeAmalgam d.radical),
      let X := Z d.radical z ⊓ centralizer (P : Set (FreeAmalgam d.radical))
      let H₀ := ⁅Z d.radical z,P⁆
      let A₀ := U d.radical z ⊓ centralizer (Ltilde d.radical z : Set (FreeAmalgam d.radical))
      HasMarkedHyperplane h d z t P B ∧ Q d.radical z ≤ P ∧ P ≤ Q d.radical t ∧ B ≤ Q d.radical t ∧
      P=Q d.radical t ⊓ centralizer (X : Set (FreeAmalgam d.radical)) ∧
      X.relIndex (Z d.radical z)=2^n ∧
      Z d.radical t ≤ X ∧ ⁅Z d.radical a,Z d.radical z⁆ ≤ X ∧
      (∀ b : FreeAmalgam d.radical, b ∈ B ↔ b ∈ Q d.radical t ∧ ∀ x ∈ X, ⁅b,x⁆ ∈ H₀) ∧
      Disjoint ⁅X,B⁆ A₀ ∧ Nat.card (⁅X,B⁆ : Subgroup (FreeAmalgam d.radical))=2^n ∧
      H₀=⁅X,B⁆ ⊔ A₀ ∧ H₀ ≤ ⁅Z d.radical a,Z d.radical z⁆ ∧ B.relIndex (Q d.radical t)=2^n ∧
      (¬ Z d.radical a ⊓ centralizer (X : Set (FreeAmalgam d.radical)) ≤ Q d.radical z →
        A₀=⁅X,Z d.radical a⁆ ⊓ H₀) := by
  obtain ⟨⟨cv⟩,_,_,_⟩ := source_four_large_plane_cover h d g hb hsat path hat hzt c c' hcritical
  obtain ⟨k,hk⟩ := cv.plane_image
  obtain ⟨P,B,hP,hB,hpoint,_,hfix,hmem,_⟩ := plane_cover_hyperplane_attachment h d cv k hk
  have hm : HasMarkedHyperplane h d z t P B := ⟨cv,k,hk,hP,hB,hpoint,hfix,hmem⟩
  obtain ⟨hQ,hP,hB,hpoint,hi,hCX,hRX,hmem,hdis,hcard,hjoin,hR,hBi⟩ :=
    marked_hyperplane_geometry h d g hb hsat path hat hzt c c' hcritical P B hm
  refine ⟨P,B,hm,hQ,hP,hB,hpoint,hi,hCX,hRX,hmem,hdis,hcard,hjoin,hR,hBi,?_⟩
  exact source_four_large_marked_attachment_intersection h d g hb hsat path hat hzt c c'
    hcritical hne P B hm

end CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic.SaturatedDistanceTwo

public noncomputable section
open Matrix Subgroup Theory.GroupTheory Representation Representation.BinaryOffender Representation.OneCohomology
open Representation.SymplecticFourOrthogonalCover
open Theory.SpecificGroups.SymplecticFour
open scoped commutatorElement IsMulCommutative

private theorem plane_displacement_le {F : Type*} [Field F] [CharP F 2] :
    displacementSpace (planeRadicalAmbient (F := F)) ≤ plane F := by
  apply Submodule.span_le.mpr
  rintro _ ⟨⟨g,v⟩,rfl⟩
  obtain ⟨C,hC⟩ := (SymplecticConjugatePair.mem_planeRadical_iff g.val).mp g.property
  change g.val • v-v ∈ plane F
  rw [←hC]
  intro i
  fin_cases i <;> simp [Plane.shearSp,mulVec,dotProduct,
    Fintype.sum_sum_type,Fin.sum_univ_two,fromBlocks]

private theorem plane_line_marking
    {F : Type*} [Field F] [Finite F] [CharP F 2] [Algebra (ZMod 2) F]
    {n : ℕ} (hF : Nat.card F=2^n) (hn : 1<n)
    (T X : Subgroup (Sp F)) (hXT : X ≤ T)
    (hT : ∃ k : Sp F, T.map (MulAut.conj k).toMonoidHom=planeRadicalAmbient)
    (hd : Module.finrank F (displacementSpace X)=1) :
    ∃ k : Sp F, T.map (MulAut.conj k).toMonoidHom=planeRadicalAmbient ∧
      (displacementSpace X).map (toLinear k).toLinearMap=point F := by
  obtain ⟨k₀,hk₀⟩ := hT
  let V := (displacementSpace X).map (toLinear k₀).toLinearMap
  have hVdim : Module.finrank F V=1 := ((toLinear k₀).finrank_map_eq _).trans hd
  have hVT : displacementSpace X ≤ displacementSpace T := by
    apply Submodule.span_le.mpr
    rintro _ ⟨⟨x,v⟩,rfl⟩
    exact Coinvariants.sub_mem_ker (ρ := (symplecticNatural 2).comp T.subtype) ⟨x.val,hXT x.property⟩ v
  have hVP : V ≤ plane F := by
    apply (Submodule.map_mono hVT).trans
    rw [←PointRadicalAction.displacement_conjugate,hk₀]
    exact plane_displacement_le
  have hVne : V ≠ ⊥ := by intro he; rw [he,finrank_bot] at hVdim; omega
  obtain ⟨v,hv,hv0⟩ := V.ne_bot_iff.mp hVne
  obtain ⟨l,hl⟩ := SylowFlag.secondPlane_transitive v (Theory.SpecificGroups.SymplecticFour.e (F := F) 0)
    ((SylowFlag.secondPlane_eq_plane (K := F)).symm ▸ hVP hv)
    ((SylowFlag.secondPlane_eq_plane (K := F)).symm ▸ e_mem_plane 0) hv0
    (by intro hh; have he := congrFun hh (.inl 0); simp [Theory.SpecificGroups.SymplecticFour.e] at he)
  let l₀ : Sp F := l.val.val
  have hlP : l₀ ∈ planeParabolic := by
    apply (mem_stabilizer_iff (plane F) l₀).mpr
    intro w hw
    have hh := (l.property w).mpr (show w ∈ (secondPlane (K := F)).restrictScalars (ZMod 2) from
      (SylowFlag.secondPlane_eq_plane (K := F)).symm ▸ hw)
    exact (SylowFlag.secondPlane_eq_plane (K := F)) ▸ hh
  have hlT : planeRadicalAmbient.map (MulAut.conj l₀).toMonoidHom=
      planeRadicalAmbient (F := F) := mem_normalizer_iff_map_conj_eq.mp
    ((planeRadicalAmbient_normalizer hF hn).symm ▸ hlP)
  have hpoint : V.map (toLinear l₀).toLinearMap=point F := by
    have he : e 0 ∈ V.map (toLinear l₀).toLinearMap := ⟨v,hv,hl⟩
    have hp : point F ≤ V.map (toLinear l₀).toLinearMap :=
      Submodule.span_le.mpr (by rintro x (rfl : x=Theory.SpecificGroups.SymplecticFour.e 0); exact he)
    apply (Submodule.eq_of_le_of_finrank_eq hp ?_).symm
    change Module.finrank F (point F)=_
    rw [(toLinear l₀).finrank_map_eq,hVdim,finrank_point]
  have hmap : (displacementSpace X).map (toLinear (l₀*k₀)).toLinearMap=
      V.map (toLinear l₀).toLinearMap := by
    ext x
    constructor
    · rintro ⟨v,hv,rfl⟩
      exact ⟨k₀ • v,⟨v,hv,rfl⟩,(mul_smul l₀ k₀ v).symm⟩
    · rintro ⟨w,⟨v,hv,rfl⟩,rfl⟩
      exact ⟨v,hv,mul_smul l₀ k₀ v⟩
  refine ⟨l₀*k₀,?_,hmap.trans hpoint⟩
  have he : (MulAut.conj (l₀*k₀)).toMonoidHom=
      (MulAut.conj l₀).toMonoidHom.comp (MulAut.conj k₀).toMonoidHom := by
    ext x
    simp [MulAut.conj_apply,mul_assoc]
  rw [he,←Subgroup.map_map,hk₀,hlT]

private theorem orthogonal_marking
    {F : Type*} [Field F] (V : Submodule F (Vector F)) (k : Sp F)
    (hk : V.map (toLinear k).toLinearMap=point F) (w : Vector F) :
    w ∈ (form F).orthogonal V ↔ (k • w) (.inr 0)=0 := by
  have he : w ∈ (form F).orthogonal V ↔ k • w ∈ (form F).orthogonal (point F) := by
    rw [←hk]
    constructor
    · rintro hw _ ⟨v,hv,rfl⟩
      exact (preserves_form k v w).trans (hw v hv)
    · intro hw v hv
      exact (preserves_form k v w).symm.trans (hw (k • v) ⟨v,hv,rfl⟩)
  rw [he]
  constructor
  · intro hw
    have hh := hw (e 0) (Submodule.subset_span (Set.mem_singleton _))
    simpa [form_apply,Theory.SpecificGroups.SymplecticFour.e] using hh
  · intro hw v hv
    obtain ⟨r,rfl⟩ := Submodule.mem_span_singleton.mp hv
    change form F (r • e 0) (k • w)=0
    simp [form_apply,Theory.SpecificGroups.SymplecticFour.e,hw]

private theorem fixed_cover_marking
    {F W G : Type*} [Field F] [Finite F] [CharP F 2] [Algebra (ZMod 2) F]
    [AddCommGroup W] [Module (ZMod 2) W] [FiniteDimensional (ZMod 2) W] [Group G]
    {σ : Representation (ZMod 2) (L (K := F)) W}
    (p : σ.IntertwiningMap (binaryNatural (K := F))) (hp : IsCover p)
    (j : Multiplicative W →* G) (hj : Function.Injective j)
    (X : Subgroup G) (β : X →* L (K := F))
    (hact : ∀ x : X, ∀ w : W, j (Multiplicative.ofAdd (σ (β x) w))=
      x.val*j (Multiplicative.ofAdd w)*x.val⁻¹)
    (k : Sp F)
    (hk : (displacementSpace ((commutator (Sp F)).subtype.comp β).range).map
      (toLinear k).toLinearMap=point F) (w : W) :
    j (Multiplicative.ofAdd w) ∈ centralizer (X : Set G) ↔ (k • p w) (.inr 0)=0 := by
  have hf : j (Multiplicative.ofAdd w) ∈ centralizer (X : Set G) ↔
      p w ∈ TwoLocalCover.fixedSpace ((commutator (Sp F)).subtype.comp β).range := by
    constructor
    · rintro hw a ⟨x,rfl⟩
      have he : σ (β x) w=w := by
        apply Multiplicative.ofAdd.injective
        apply hj
        rw [hact,hw x.val x.property,mul_inv_cancel_right]
      exact (LinearMap.congr_fun (p.isIntertwining' (β x)) w).symm.trans (congrArg p he)
    · intro hw x hx
      have he := cover_fixed_of_projection_fixed p hp (β ⟨x,hx⟩) w
        (hw ((commutator (Sp F)).subtype (β ⟨x,hx⟩)) ⟨⟨x,hx⟩,rfl⟩)
      have hh := congrArg (fun v => j (Multiplicative.ofAdd v)) he
      rw [hact,mul_inv_eq_iff_eq_mul] at hh
      exact hh
  rw [hf,←orthogonal_displacementSpace]
  exact orthogonal_marking _ k hk (p w)

private theorem cover_moving_index
    {F W G : Type*} [Field F] [Finite F] [CharP F 2] [Algebra (ZMod 2) F]
    [AddCommGroup W] [Module (ZMod 2) W] [FiniteDimensional (ZMod 2) W] [Group G]
    (σ : Representation (ZMod 2) (L (K := F)) W)
    (p : σ.IntertwiningMap (binaryNatural (K := F))) (hp : IsCover p)
    (U A : Subgroup G) (j : Multiplicative W →* G) (hj : Function.Injective j)
    (hjr : j.range=U) (β : A →* L (K := F))
    (hact : ∀ (a : A) (w : W), j (Multiplicative.ofAdd (σ (β a) w))=
      a.val*j (Multiplicative.ofAdd w)*a.val⁻¹) :
    (centralizer (A : Set G)).relIndex U =
      Nat.card F ^ Module.finrank F
        (displacementSpace ((commutator (Sp F)).subtype.comp β).range) := by
  let α := (commutator (Sp F)).subtype.comp β
  have hi := embedded_centralizer_index σ U A j hj hjr β hact
  rw [fixedCodim_of_binaryCover p hp] at hi
  have hfixed : fixedSpace (binaryNatural (K := F)) β.range =
      (TwoLocalCover.fixedSpace α.range).restrictScalars (ZMod 2) := by
    ext v
    constructor
    · intro hv x hx
      obtain ⟨a,rfl⟩ := hx
      exact hv ⟨β a,⟨a,rfl⟩⟩
    · intro hv x
      obtain ⟨a,ha⟩ := x.property
      change binaryNatural x.val v=v
      rw [←ha]
      exact hv (α a) ⟨a,rfl⟩
  rw [hi]
  change 2 ^ Module.finrank (ZMod 2)
    (Vector F ⧸ fixedSpace (binaryNatural (K := F)) β.range)=_
  rw [hfixed]
  have hc := Nat.card_congr (Submodule.Quotient.restrictScalarsEquiv (ZMod 2)
    (TwoLocalCover.fixedSpace α.range)).toEquiv
  rw [Module.natCard_eq_pow_finrank (K := ZMod 2),Nat.card_zmod] at hc
  rw [hc,fixed_quotient_card]



private theorem central_supplement_fixed_index {G : Type*} [Group G]
    (V C D A : Subgroup G) [Finite D] [IsMulCommutative D]
    (hVD : V ≤ D) (hCD : C ≤ D) (hgen : D=V ⊔ C)
    (hCA : C ≤ centralizer (A : Set G)) :
    (centralizer (A : Set G)).relIndex D=(centralizer (A : Set G)).relIndex V := by
  let X := D ⊓ centralizer (A : Set G)
  have hCX : C ≤ X := le_inf hCD hCA
  have hVX : V ⊔ X=D := le_antisymm (sup_le hVD inf_le_left)
    (hgen.le.trans (sup_le le_sup_left (hCX.trans le_sup_right)))
  have hXU : X ≤ normalizer (V : Set G) :=
    (inf_le_left.trans (D.le_centralizer.trans (centralizer_le hVD))).trans
      (Subgroup.centralizer_le_normalizer _)
  let : Finite X := Finite.of_injective (inclusion (show X ≤ D from inf_le_left))
    (inclusion_injective _)
  have he : X ⊓ V=V ⊓ centralizer (A : Set G) := by
    ext x
    exact ⟨fun hx => ⟨hx.2,hx.1.2⟩,fun hx => ⟨⟨hVD hx.1,hx.2⟩,hx.1⟩⟩
  calc
    _ = X.relIndex D := (inf_relIndex_left _ _).symm
    _ = X.relIndex (V ⊔ X) := congrArg (X.relIndex ·) hVX.symm
    _ = X.relIndex V := relIndex_sup_of_normalizes V X hXU
    _ = _ := by rw [←inf_relIndex_right,he,inf_relIndex_left]


open Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
namespace CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic.SaturatedDistanceTwo
open DistanceTwoRecognition ChapterB.QuasisimpleSource
variable {H F : Type*} [Group H] [Finite H] [Field F] [Finite F] [CharP F 2]
variable {K R : Subgroup H} {n : ℕ} (h : Input K R n F)
variable (d : CharacteristicReduction K R)
include h

omit [Finite H] [Field F] [Finite F] [CharP F 2] h in
private theorem midpoint_centralizes_radical
    {z t : Vertex d.radical} (hz : color d.radical z=false)
    (hzt : Adjacent d.radical z t) :
    Z d.radical t ≤ centralizer (Q d.radical t : Set (FreeAmalgam d.radical)) := by
  have ht : color d.radical t=true := by
    apply Bool.eq_true_of_not_eq_false
    intro he
    exact adjacent_color_ne d.radical hzt (hz.trans he.symm)
  rw [show Z d.radical t=omegaCenter (Q d.radical t) by simp [Z,ht,edgeOmega]]
  exact fun x hx => (mem_omegaCenter_iff.mp hx).2.2

/-- The full centralizer index for any subgroup of the actual plane radical. -/
theorem plane_cover_full_fixed_index
    (g : Geometry d.radical) (hb : g.b d.radical=2)
    {z t : Vertex d.radical} (hz : color d.radical z=false)
    (hzt : Adjacent d.radical z t)
    (cv : RadicalPlaneCover d.radical (replacementMovedSection h d) n z t)
    (A : Subgroup (FreeAmalgam d.radical)) (hA : A ≤ Q d.radical t) :
    (centralizer (A : Set (FreeAmalgam d.radical))).relIndex (Z d.radical z)=
      (2^n)^Module.finrank cv.field.Carrier (displacementSpace
        (((commutator (Sp cv.field.Carrier)).subtype.comp cv.actor).comp (inclusion hA)).range) := by
  let := g.Z_elementary (by omega : 0 < g.b d.radical) z hz
  let := finite_Z d.radical z
  have he := central_supplement_fixed_index (U d.radical z) (Z d.radical t) (Z d.radical z) A
    (U_le_Z z) (Sp4Four.edge_Z_le_endpoint d.radical hz hzt)
    (Z_eq_moving_sup_edge_of_distance_two h d g hb hz hzt)
    ((midpoint_centralizes_radical d hz hzt).trans (centralizer_le hA))
  have hm := cover_moving_index (MovedSection.coverAction (replacementMovedSection h d) cv.equiv)
    (MovedSection.coverProjection (replacementMovedSection h d) cv.equiv) cv.cover (U d.radical z) A
    cv.embedding cv.injective cv.range_eq (cv.actor.comp (inclusion hA))
    (fun x w => cv.actor_conjugation (inclusion hA x) w)
  have hFc : Nat.card cv.field.Carrier=2^n := cv.field.card_eq.trans (congrArg (2^·) cv.degree)
  exact he.trans (hm.trans (congrArg (·^_) hFc))


/-- A field-index centralizer determines its actual dual marked hyperplane. -/
theorem plane_cover_dual_marked_hyperplane
    (g : Geometry d.radical) (hb : g.b d.radical=2)
    {z t : Vertex d.radical} (hz : color d.radical z=false)
    (hzt : Adjacent d.radical z t)
    (cv : RadicalPlaneCover d.radical (replacementMovedSection h d) n z t)
    (A : Subgroup (FreeAmalgam d.radical)) (hA : A ≤ Q d.radical t)
    (hi : (centralizer (A : Set (FreeAmalgam d.radical))).relIndex (Z d.radical z)=2^n) :
    ∃ P B : Subgroup (FreeAmalgam d.radical),
      let Y := Z d.radical z ⊓ centralizer (A : Set (FreeAmalgam d.radical))
      HasMarkedHyperplane h d z t P B ∧ P ≤ Q d.radical t ∧
      P=Q d.radical t ⊓ centralizer (Y : Set (FreeAmalgam d.radical)) ∧
      Z d.radical z ⊓ centralizer (P : Set (FreeAmalgam d.radical))=Y := by
  let α := (commutator (Sp cv.field.Carrier)).subtype.comp cv.actor
  let β := cv.actor.comp (inclusion hA)
  let αA := α.comp (inclusion hA)
  have hd : Module.finrank cv.field.Carrier (displacementSpace αA.range)=1 := by
    have hh := plane_cover_full_fixed_index h d g hb hz hzt cv A hA
    have hh' : 2^n=(2^n)^Module.finrank cv.field.Carrier (displacementSpace αA.range) := hi.symm.trans hh
    have hq : 1 < 2^n := one_lt_pow₀ (by decide : 1 < (2:ℕ)) (by have := h.nonbinary; omega)
    exact Nat.pow_right_injective hq (hh'.symm.trans (pow_one _).symm)
  have hAT : αA.range ≤ α.range := by rintro _ ⟨a,rfl⟩; exact ⟨inclusion hA a,rfl⟩
  obtain ⟨k,hk,hdline⟩ := plane_line_marking
    (cv.field.card_eq.trans (congrArg (2^·) cv.degree)) h.nonbinary
    α.range αA.range hAT cv.plane_image hd
  let p := MovedSection.coverProjection (replacementMovedSection h d) cv.equiv
  have hfixA (w : (replacementMovedSection h d).space.toSubmodule) :
      cv.embedding (Multiplicative.ofAdd w) ∈ centralizer (A : Set (FreeAmalgam d.radical)) ↔
        (k • p w) (.inr 0)=0 :=
    fixed_cover_marking p cv.cover cv.embedding cv.injective A β
      (fun a w => cv.actor_conjugation (inclusion hA a) w) k hdline w
  obtain ⟨P,B,hP,hB,hpoint,hindex,hfix,hmem,_⟩ := plane_cover_hyperplane_attachment h d cv k hk
  have hm : HasMarkedHyperplane h d z t P B := ⟨cv,k,hk,hP,hB,hpoint,hfix,hmem⟩
  have hUeq : U d.radical z ⊓ centralizer (P : Set (FreeAmalgam d.radical)) =
      U d.radical z ⊓ centralizer (A : Set (FreeAmalgam d.radical)) := by
    ext x
    constructor
    · rintro ⟨hx,hc⟩
      refine ⟨hx,?_⟩
      obtain ⟨w,rfl⟩ := cv.range_eq.symm ▸ hx
      exact (hfixA w.toAdd).mpr ((hfix w.toAdd).mp hc)
    · rintro ⟨hx,hc⟩
      refine ⟨hx,?_⟩
      obtain ⟨w,rfl⟩ := cv.range_eq.symm ▸ hx
      exact (hfix w.toAdd).mpr ((hfixA w.toAdd).mp hc)
  let C := Z d.radical t
  have hCT : C ≤ centralizer (Q d.radical t : Set (FreeAmalgam d.radical)) :=
    midpoint_centralizes_radical d hz hzt
  have hCZ : C ≤ Z d.radical z := Sp4Four.edge_Z_le_endpoint d.radical hz hzt
  let := g.Z_elementary (by omega : 0 < g.b d.radical) z hz
  have hCU : C ≤ normalizer (U d.radical z : Set (FreeAmalgam d.radical)) :=
    (hCZ.trans ((Z d.radical z).le_centralizer.trans (centralizer_le (U_le_Z z)))).trans
      (Subgroup.centralizer_le_normalizer _)
  have hCP : C ≤ centralizer (P : Set (FreeAmalgam d.radical)) := hCT.trans (centralizer_le hP)
  have hCA : C ≤ centralizer (A : Set (FreeAmalgam d.radical)) := hCT.trans (centralizer_le hA)
  have hgen := Z_eq_moving_sup_edge_of_distance_two h d g hb hz hzt
  have hXP : Z d.radical z ⊓ centralizer (P : Set (FreeAmalgam d.radical)) =
      (U d.radical z ⊓ centralizer (P : Set (FreeAmalgam d.radical))) ⊔ C := by
    rw [hgen,sup_comm (U d.radical z),inf_centralizer_sup_of_centralizing C
      (U d.radical z) P hCU hCP,sup_comm]
  have hYA : Z d.radical z ⊓ centralizer (A : Set (FreeAmalgam d.radical)) =
      (U d.radical z ⊓ centralizer (A : Set (FreeAmalgam d.radical))) ⊔ C := by
    rw [hgen,sup_comm (U d.radical z),inf_centralizer_sup_of_centralizing C
      (U d.radical z) A hCU hCA,sup_comm]
  have heq : Z d.radical z ⊓ centralizer (P : Set (FreeAmalgam d.radical)) =
      Z d.radical z ⊓ centralizer (A : Set (FreeAmalgam d.radical)) := by rw [hXP,hYA,hUeq]
  refine ⟨P,B,hm,hP,?_,heq⟩
  apply le_antisymm
  · refine le_inf hP ?_
    rw [hYA,←hUeq]
    apply le_centralizer_iff.mpr
    exact sup_le (le_centralizer_iff.mp (hpoint.le.trans inf_le_right)) hCP
  · have hle : U d.radical z ⊓ centralizer (P : Set (FreeAmalgam d.radical)) ≤
        Z d.radical z ⊓ centralizer (A : Set (FreeAmalgam d.radical)) := by
      rw [hYA,←hUeq]; exact le_sup_left
    exact (inf_le_inf_left _ (centralizer_le hle)).trans hpoint.ge

end CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic.SaturatedDistanceTwo

open Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
namespace CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic.SaturatedDistanceTwo
open DistanceTwoRecognition ChapterB.QuasisimpleSource
variable {H F : Type*} [Group H] [Finite H] [Field F] [Finite F] [CharP F 2]
variable {K R : Subgroup H} {n : ℕ} (h : Input K R n F)
variable (d : CharacteristicReduction K R)
include h

/-- The escaping-centralizer branch of source (4) is impossible when the
complete attachments differ. The opposite hyperplane is marked from its
actual field-linear fixed space, then the two intersection identities use
the same pair of hyperplanes and the original covering maps. -/
theorem source_four_large_marked_centralizer_le
    (g : Geometry d.radical) (hb : g.b d.radical=2)
    (hsat : (normalizer (d.radical : Set d.overgroup)).pCoreIn 2=d.radical)
    {a z t : Vertex d.radical} (path : CriticalPath d.radical g a z)
    (hat : Adjacent d.radical a t) (hzt : Adjacent d.radical z t)
    (c : EdgeMarking h d a t) (c' : EdgeMarking h d z t)
    (hcritical : (2^n)^2 ≤ (Q d.radical z).relIndex (Z d.radical a))
    (hne : U d.radical a ⊓ centralizer (Ltilde d.radical a : Set (FreeAmalgam d.radical)) ≠
      U d.radical z ⊓ centralizer (Ltilde d.radical z : Set (FreeAmalgam d.radical)))
    (P B : Subgroup (FreeAmalgam d.radical))
    (hmarked : HasMarkedHyperplane h d z t P B) :
    Z d.radical a ⊓ centralizer
      (Z d.radical z ⊓ centralizer (P : Set (FreeAmalgam d.radical)) : Set (FreeAmalgam d.radical)) ≤ Q d.radical z := by
  by_contra hescape
  let X := Z d.radical z ⊓ centralizer (P : Set (FreeAmalgam d.radical))
  let Y := Z d.radical a ⊓ centralizer (X : Set (FreeAmalgam d.radical))
  let C := Z d.radical t
  obtain ⟨hQ,hP,hB,hpoint,hi,hCX,hRX,hmem,hdis,hcard,hjoin,hR,hBi⟩ :=
    marked_hyperplane_geometry h d g hb hsat path hat hzt c c' hcritical P B hmarked
  obtain ⟨hYi,_,hPY,hHY⟩ := source_four_large_escaping_hyperplane h d g hb hsat
    path hat hzt c c' hcritical P hP hpoint hi hescape
  have hzQ : Z d.radical z ≤ Q d.radical z :=
    (g.omega_bound z path.end_color (by
      rw [g.distance_constant z path.end_color]; change 0 < g.b d.radical; omega)).trans
      (omegaCenter_le _)
  have hXT : X ≤ Q d.radical t := inf_le_left.trans (hzQ.trans c'.core_le_edge)
  have hQU : Q d.radical z ≤ centralizer (Z d.radical z : Set (FreeAmalgam d.radical)) :=
    le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp
      (Z_centralizes_Q d.radical z path.end_color))
  have hYX : Z d.radical z ⊓ centralizer (Y : Set (FreeAmalgam d.radical))=X := by
    apply le_antisymm
    · apply le_inf inf_le_left
      apply le_centralizer_iff.mpr
      rw [hPY]
      exact sup_le (hQU.trans (centralizer_le inf_le_left))
        (le_centralizer_iff.mp (show Z d.radical z ⊓ centralizer (Y : Set (FreeAmalgam d.radical)) ≤
          centralizer (Y : Set (FreeAmalgam d.radical)) from inf_le_right))
    · exact le_inf inf_le_left (le_centralizer_iff.mp (show Y ≤
        centralizer (X : Set (FreeAmalgam d.radical)) from inf_le_right))
  obtain ⟨⟨cv⟩,_,hai,hzi,_⟩ := source_four_large_paired_geometry h d g hb hsat
    path hat hzt c c' hcritical
  obtain ⟨P',B',hm',hP',hpY,heY⟩ := plane_cover_dual_marked_hyperplane h d g hb
    path.start_color hat cv X hXT (by rwa [inf_relIndex_left] at hYi)
  have hp' : P'=Q d.radical t ⊓ centralizer
      (Z d.radical a ⊓ centralizer (P' : Set (FreeAmalgam d.radical)) : Set (FreeAmalgam d.radical)) :=
    hpY.trans (congrArg (fun S : Subgroup (FreeAmalgam d.radical) =>
      Q d.radical t ⊓ centralizer (S : Set (FreeAmalgam d.radical))) heY.symm)
  have hi' : (Z d.radical a ⊓ centralizer (P' : Set (FreeAmalgam d.radical))).relIndex
      (Z d.radical a)=2^n := by rw [heY]; exact hYi
  obtain ⟨_,hzk,_,hreverse⟩ := source_four_large_midpoint_kernels h d g hb hsat
    path hat hzt c c' hcritical
  have hXnot : ¬ X ≤ Q d.radical a := by
    intro hle
    have he : X=C := le_antisymm
      ((le_inf (show X ≤ Z d.radical z from inf_le_left) hle).trans_eq hzk) hCX
    have hq : 1 < 2^n := one_lt_pow₀ (by decide : 1 < (2:ℕ)) (by have := h.nonbinary; omega)
    change X.relIndex (Z d.radical z)=2^n at hi
    rw [he,hzi] at hi
    nlinarith only [hq,hi]
  have hreverseX : Z d.radical z ⊓ centralizer
      (Z d.radical a ⊓ centralizer (P' : Set (FreeAmalgam d.radical)) : Set (FreeAmalgam d.radical))=X :=
    (congrArg (fun S : Subgroup (FreeAmalgam d.radical) =>
      Z d.radical z ⊓ centralizer (S : Set (FreeAmalgam d.radical))) heY).trans hYX
  have hescape' : ¬ Z d.radical z ⊓ centralizer
      (Z d.radical a ⊓ centralizer (P' : Set (FreeAmalgam d.radical)) : Set (FreeAmalgam d.radical)) ≤ Q d.radical a :=
    fun hle => hXnot (hreverseX.ge.trans hle)
  have hedge := MSCentralOrbit.edgeCentralizerCondition d.radical (replacement_isPGroup h d)
    (replacement_core_le h d) (replacement_omegaOrbit_centralizer h d)
  let rev : CriticalPath d.radical g z a :=
    { start_color := path.end_color
      walk := path.walk.reverse
      shortest := by rw [SimpleGraph.Walk.length_reverse,path.shortest,SimpleGraph.dist_comm]
      critical := critical_reverse d.radical g hedge a path.start_color
        (by rw [g.distance_constant a path.start_color]; change 0 < g.b d.radical; omega)
        z path.end_color path.critical }
  have hr : (2^n)^2 ≤ (Q d.radical a).relIndex (Z d.radical z) := hreverse.ge
  have hA₀ := source_four_large_marked_attachment_intersection h d g hb hsat
    path hat hzt c c' hcritical hne P B hmarked hescape
  have hA₁ := source_four_large_marked_attachment_intersection h d g hb hsat
    rev hzt hat c' c hr (Ne.symm hne) P' B' hm' hescape'
  have hm := (source_four_large_escaping_hyperplane h d g hb hsat
    rev hzt hat c' c hr P' hP' hp' hi' hescape').2.2.2
  rw [heY] at hA₁
  change _=⁅Y,Z d.radical z⁆ ⊓ ⁅Z d.radical a,P'⁆ at hA₁
  have hmX : ⁅Z d.radical a,P'⁆=⁅Z d.radical a,X⁆ :=
    hm.trans (congrArg (fun S : Subgroup (FreeAmalgam d.radical) => ⁅Z d.radical a,S⁆) hreverseX)
  rw [hmX,commutator_comm Y (Z d.radical z),←hHY,commutator_comm (Z d.radical a) X] at hA₁
  exact hne (hA₁.trans ((inf_comm _ _).trans hA₀.symm))

/-- The source plane geometry supplies a genuine marked hyperplane whose
opposite centralizer lies in the endpoint core whenever the attachments differ.
The complete complement and original movement data are retained. -/
theorem source_four_large_unequal_nonescaping_hyperplane
    (g : Geometry d.radical) (hb : g.b d.radical=2)
    (hsat : (normalizer (d.radical : Set d.overgroup)).pCoreIn 2=d.radical)
    {a z t : Vertex d.radical} (path : CriticalPath d.radical g a z)
    (hat : Adjacent d.radical a t) (hzt : Adjacent d.radical z t)
    (c : EdgeMarking h d a t) (c' : EdgeMarking h d z t)
    (hcritical : (2^n)^2 ≤ (Q d.radical z).relIndex (Z d.radical a))
    (hne : U d.radical a ⊓ centralizer (Ltilde d.radical a : Set (FreeAmalgam d.radical)) ≠
      U d.radical z ⊓ centralizer (Ltilde d.radical z : Set (FreeAmalgam d.radical))) :
    ∃ P B : Subgroup (FreeAmalgam d.radical),
      let X := Z d.radical z ⊓ centralizer (P : Set (FreeAmalgam d.radical))
      let H₀ := ⁅Z d.radical z,P⁆
      let A₀ := U d.radical z ⊓ centralizer (Ltilde d.radical z : Set (FreeAmalgam d.radical))
      HasMarkedHyperplane h d z t P B ∧ Q d.radical z ≤ P ∧ P ≤ Q d.radical t ∧ B ≤ Q d.radical t ∧
      P=Q d.radical t ⊓ centralizer (X : Set (FreeAmalgam d.radical)) ∧
      X.relIndex (Z d.radical z)=2^n ∧
      Z d.radical t ≤ X ∧ ⁅Z d.radical a,Z d.radical z⁆ ≤ X ∧
      (∀ b : FreeAmalgam d.radical, b ∈ B ↔ b ∈ Q d.radical t ∧ ∀ x ∈ X, ⁅b,x⁆ ∈ H₀) ∧
      Disjoint ⁅X,B⁆ A₀ ∧ Nat.card (⁅X,B⁆ : Subgroup (FreeAmalgam d.radical))=2^n ∧
      H₀=⁅X,B⁆ ⊔ A₀ ∧ H₀ ≤ ⁅Z d.radical a,Z d.radical z⁆ ∧ B.relIndex (Q d.radical t)=2^n ∧
      Z d.radical a ⊓ centralizer (X : Set (FreeAmalgam d.radical)) ≤ Q d.radical z := by
  obtain ⟨P,B,hm,hQ,hP,hB,hpoint,hi,hCX,hRX,hmem,hdis,hcard,hjoin,hR,hBi,_⟩ :=
    source_four_large_unequal_marked_intersection h d g hb hsat path hat hzt c c' hcritical hne
  exact ⟨P,B,hm,hQ,hP,hB,hpoint,hi,hCX,hRX,hmem,hdis,hcard,hjoin,hR,hBi,
    source_four_large_marked_centralizer_le h d g hb hsat path hat hzt c c' hcritical hne P B hm⟩

end CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic.SaturatedDistanceTwo
