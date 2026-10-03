module
public import Stellmacher.SectionNine.DistanceOneAction
public import Stellmacher.SectionThree.LemmaThreeFiveOmega
public import Theory.ElementaryAbelian.ProductCenter
public import Stellmacher.TwoResidualFixedCentralizer

/-!
# The extracted residual centralizes the distance-one product center

For the actual distance-one action data, let C and D be the two center and
stabilizer intersections, and V their product. This module proves relation
(3) of Stellmacher (9.1): O²(E) centralizes Z(V), with the same extracted
conjugator and group E. Only the ambient Section Nine context, critical
length one, and the already proved action data are used.

The elementary factors normalize one another, so their product center is
an elementary abelian two-group. Relation (1) shows that E normalizes V
and that its action on Z(V) commutes with the two-core Q of the terminal
stabilizer P. The Q-fixed subgroup of Z(V) lies in Z(Q), because P is of
characteristic two type. Lemma (3.5), applied to Z(Q), and the central
Sylow omega-center in (7.5) show that O²(P) centralizes Z(Q). Residual
functoriality therefore gives the required fixed-subgroup centralization
by O²(E). The general P × Q fixed-space kernel theorem makes the residual
image on Z(V) a two-group; residual-perfectness makes that image trivial.
This proves the source transfer without needing a separate identification
of the fixed subgroup with the terminal vertex center.

The intermediate theorem `next_core_center_residual` is also public: for
any commuting critical pair in the Section Seven configuration, the next
stabilizer's residual centralizes the center of its two-core. It has no
critical-length or Section Nine conclusion hypothesis. The maximal-subgroup
seed and chief-factor quotient arguments use this exact ambient center
centralization independently of relation (3). The public `twoResidualIn_mono`
also supplies the subgroup-to-overgroup residual containment used by the seed.

Source: Stellmacher, Journal of Algebra190 (1997), p.46 / PDF36,
`refs/files/stellmacher-n-group.pdf`, proof of (9.1), relation (3), together
with the proved (3.5) and (7.5).
-/

namespace Stellmacher.SectionNine
open Stellmacher.Later Stellmacher.SectionsFiveToSeven CosetGraphContext SevenSix
open scoped Pointwise commutatorElement
universe u

public theorem next_core_center_residual
    {G : Type u} [Group G] [Finite G] {T A B : Subgroup G}
    (h : SectionSevenHypotheses G T A B)
    (Γ : CosetGraphContext G T A B) (cp : CriticalPath Γ)
    (hcomm : ⁅z Γ cp.a, z Γ cp.a'⁆ = ⊥) :
    ⁅(Subgroup.center (q Γ cp.firstStep)).map (q Γ cp.firstStep).subtype,
      twoResidualIn (stabilizer Γ cp.firstStep)⁆ = ⊥ := by
  let P := stabilizer Γ cp.firstStep
  let Q := q Γ cp.firstStep
  let Z := (Subgroup.center Q).map Q.subtype
  have hQeq : Q = twoCoreAmbient P := by
    change q Γ cp.firstStep = twoCoreAmbient (stabilizer Γ cp.firstStep)
    rw [q, Γ.twoCoreAt_def]
    rfl
  have hQP : Q ≤ P := hQeq ▸ Subgroup.map_subtype_le _
  have hZQ : Z ≤ Q := Subgroup.map_subtype_le _
  have hPN : P ≤ Subgroup.normalizer (Z : Set G) :=
    (stabilizer_le_normalizer_q Γ cp.firstStep).trans
      (BenderSuzuki.External.hkt_normalizer_le_normalizer_map_subtype_of_characteristic Q
        (Subgroup.center Q))
  have hnormal : (Z.subgroupOf P).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer (hZQ.trans hQP)).mpr hPN
  have hfixed : ⁅Z, twoCoreAmbient P ⊓ twoResidualAmbient P⁆ = ⊥ := by
    apply Subgroup.commutator_eq_bot_iff_le_centralizer.mpr
    exact (centerAmbient_le_centralizer Q).trans (Subgroup.centralizer_le
      (hQeq ▸ (inf_le_left : twoCoreAmbient P ⊓ twoResidualAmbient P ≤ twoCoreAmbient P)))
  have h75 := (lemma_seven_five h Γ cp hcomm).next_center.2
  have hOmega : ⁅omegaOneCenterAmbient T, twoResidualAmbient P⁆ = ⊥ := by
    apply Subgroup.commutator_eq_bot_iff_le_centralizer.mpr
    change omegaOneCenter T ≤ _
    rw [← (lemma_seven_five h Γ cp hcomm).next_center.1, h75]
    exact ((omegaOneCenter_le_centerAmbient P).trans (centerAmbient_le_centralizer P)).trans
      (Subgroup.centralizer_le (Subgroup.map_subtype_le _))
  have hlocal := (edge_local_data h Γ cp).2
  exact (SectionThree.lemma_three_five_omega T (sectionThreeHypotheses h) P ((pFamily_iff_pSet ⊤ T P).mp hlocal.1) Z
    ⟨hZQ.trans hQP, hZQ.trans_eq hQeq, hnormal⟩ hlocal.2 hfixed).resolve_left
      (fun hn => hn hOmega)

public theorem twoResidualIn_mono {G : Type u} [Group G] [Finite G]
    (E P : Subgroup G) (hEP : E ≤ P) : twoResidualIn E ≤ twoResidualIn P := by
  let R := BenderSuzuki.External.hktPResidual 2 P
  let _ : R.Normal := BenderSuzuki.External.hktPResidual_normal
  let f := (QuotientGroup.mk' R).comp (Subgroup.inclusion hEP)
  have hfp : IsPGroup 2 (E ⧸ f.ker) :=
    ((BenderSuzuki.External.hktPResidual_quotient_isPGroup (q := 2) (Q := P)).to_subgroup
      f.range).of_equiv (QuotientGroup.quotientKerEquivRange f).symm
  have hk : twoResidualSubgroup E ≤ f.ker := by
    rw [SectionThree.twoResidualSubgroup_eq_hktPResidual']
    exact BenderSuzuki.External.hktPResidual_le f.ker inferInstance hfp
  rintro x ⟨e, he, rfl⟩
  have hm : Subgroup.inclusion hEP e ∈ R := (QuotientGroup.eq_one_iff _).mp (hk he)
  change _ ∈ (twoResidualSubgroup P).map P.subtype
  rw [SectionThree.twoResidualSubgroup_eq_hktPResidual']
  exact Subgroup.mem_map_of_mem P.subtype hm

private theorem characteristic_centralizer_le_core
    {G : Type u} [Group G] (P : Subgroup G) (hP : IsCharacteristicTwoType P) :
    P ⊓ Subgroup.centralizer (twoCoreIn P : Set G) ≤ twoCoreIn P := by
  intro x hx
  have h : (⟨x,hx.1⟩ : P) ∈ Subgroup.centralizer (pCore 2 P : Set P) := by
    intro y hy
    apply Subtype.ext
    exact hx.2 y (Subgroup.mem_map_of_mem P.subtype hy)
  exact Subgroup.mem_map_of_mem P.subtype (hP h)

private theorem elementary_of_le {G : Type u} [Group G]
    (U W : Subgroup G) [IsElementaryAbelian 2 W] (hUW : U ≤ W) :
    IsElementaryAbelian 2 U := by
  let _ : IsMulCommutative U := IsMulCommutative.of_setLike_mul_comm
    (fun x hx y hy => setLike_mul_comm (s := W) (hUW hx) (hUW hy))
  refine { exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr ?_ }
  intro x
  exact Subtype.ext (elemPow_eq_one_of_isElementaryAbelian (x : G) (hUW x.property))

private theorem distance_one_extracted_center_residual_inputs
    {H G : Type u} [Group H] [Finite H] [Group G] [Finite G]
    {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
    {embedding : G →* H} {T A B : Subgroup G}
    (ctx : AmbientSectionNineContext H S0 S P1 P2 embedding T A B)
    (hb : ctx.criticalPath.length = 1) (data : DistanceOneActionData ctx) :
    let next := ctx.Γ.act data.x⁻¹ ctx.criticalPath.a
    let C := z ctx.Γ ctx.criticalPath.a ⊓ stabilizer ctx.Γ next
    let D := z ctx.Γ next ⊓ stabilizer ctx.Γ ctx.criticalPath.a
    let Z := (Subgroup.center (C ⊔ D : Subgroup G)).map (C ⊔ D).subtype
    let Q := q ctx.Γ ctx.criticalPath.a'
    IsElementaryAbelian 2 Z ∧ IsPGroup 2 Q ∧
    data.E ≤ Subgroup.normalizer (Z : Set G) ∧
    Q ≤ Subgroup.normalizer (Z : Set G) ∧
    ⁅Q, data.E⁆ ≤ Subgroup.centralizer (Z : Set G) ∧
    ⁅Z ⊓ Subgroup.centralizer (Q : Set G), twoResidualAmbient data.E⁆ = ⊥ := by
  let Γ := ctx.Γ
  let cp := ctx.criticalPath
  let next := Γ.act data.x⁻¹ cp.a
  let C := z Γ cp.a ⊓ stabilizer Γ next
  let D := z Γ next ⊓ stabilizer Γ cp.a
  let V := C ⊔ D
  let Z := (Subgroup.center V).map V.subtype
  let Q := q Γ cp.a'
  let P := stabilizer Γ cp.a'
  have hlen : cp.length = 1 := hb
  have hstep : cp.firstStep = cp.a' := by
    calc
      cp.firstStep = cp.path ⟨1, by omega⟩ := cp.path_first.symm
      _ = cp.path ⟨cp.length, Nat.lt_succ_self _⟩ := by
        congr 1
        apply Fin.ext
        exact hb.symm
      _ = cp.a' := cp.path_end
  have hneighbor : cp.a' ∈ neighborhood Γ cp.a := by
    rw [neighborhood, Γ.neighbors_def]
    exact (Γ.distance_symm _ _).trans (cp.endpoint_distance.trans hb)
  have hback : cp.a ∈ neighborhood Γ cp.a' := by
    rw [neighborhood, Γ.neighbors_def]
    exact cp.endpoint_distance.trans hb
  let _ := z_isElementaryAbelian_of_neighbor ctx.sectionSeven Γ hneighbor
  let _ : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let _ : IsElementaryAbelian 2 (z Γ next) := by
    change IsElementaryAbelian 2 (z Γ (Γ.act data.x⁻¹ cp.a))
    rw [z_act, inv_inv]
    exact IsElementaryAbelian.map _
  let _ : IsElementaryAbelian 2 C := elementary_of_le C (z Γ cp.a) inf_le_left
  let _ : IsElementaryAbelian 2 D := elementary_of_le D (z Γ next) inf_le_left
  have hgeom := distance_one_product_factors Γ cp.a next
  let _ : IsElementaryAbelian 2 (Subgroup.center V) :=
    isElementaryAbelian_center_sup_of_normalizes C D hgeom.1
  have hZelem : IsElementaryAbelian 2 Z := IsElementaryAbelian.map V.subtype
  have hQeq : Q = twoCoreIn P := by
    change q Γ cp.a' = twoCoreIn (stabilizer Γ cp.a')
    rw [q, Γ.twoCoreAt_def]
    rfl
  have hQp : IsPGroup 2 Q := by
    rw [hQeq]
    exact (pCore_isPGroup (p := 2) (G := P)).map P.subtype
  have hfirstE : z Γ cp.a ≤ data.E := by rw [data.generated]; exact le_sup_left
  have hsecondE : z Γ next ≤ data.E := by rw [data.generated]; exact le_sup_right
  have hVE : V ≤ data.E := sup_le (inf_le_left.trans hfirstE) (inf_le_left.trans hsecondE)
  have hVP : V ≤ P := hVE.trans data.E_le
  have hQP : Q ≤ P := hQeq ▸ twoCoreIn_le P
  have hQV : Q ≤ Subgroup.normalizer (V : Set G) := by
    have hQfirst : Q ≤ stabilizer Γ cp.a :=
      ((lemma_seven_three ctx.sectionSeven Γ).sylow_and_core _ _ hback default).2.2
    have hQmap : Q.map (MulAut.conj data.x).toMonoidHom = Q :=
      Subgroup.mem_normalizer_iff_map_conj_eq.mp
        (stabilizer_le_normalizer_q Γ cp.a' data.x_mem)
    have hQnext : Q ≤ stabilizer Γ next := by
      change Q ≤ stabilizer Γ (Γ.act data.x⁻¹ cp.a)
      rw [stabilizer_act, inv_inv, ← hQmap]
      exact Subgroup.map_mono hQfirst
    have hQC : Q ≤ Subgroup.normalizer (C : Set G) :=
      (le_inf (hQfirst.trans (stabilizer_le_normalizer_z Γ _))
        (hQnext.trans Subgroup.le_normalizer)).trans Subgroup.inf_normalizer_le_normalizer_inf
    have hQD : Q ≤ Subgroup.normalizer (D : Set G) :=
      (le_inf (hQnext.trans (stabilizer_le_normalizer_z Γ _))
        (hQfirst.trans Subgroup.le_normalizer)).trans Subgroup.inf_normalizer_le_normalizer_inf
    exact (le_inf hQC hQD).trans (Subgroup.normalizer_inf_normalizer_le_normalizer_sup C D)
  have hEV : data.E ≤ Subgroup.normalizer (V : Set G) :=
    Subgroup.le_normalizer_iff_commutator_le_left.mpr
      ((Subgroup.commutator_mono le_sup_left le_rfl).trans data.product_action)
  have hZnormal := BenderSuzuki.External.hkt_normalizer_le_normalizer_map_subtype_of_characteristic
    V (Subgroup.center V)
  have hZV : Z ≤ V := Subgroup.map_subtype_le _
  have hZcentralV : Z ≤ Subgroup.centralizer (V : Set G) := centerAmbient_le_centralizer V
  have hQE : ⁅Q,data.E⁆ ≤ Subgroup.centralizer (Z : Set G) :=
    ((Subgroup.commutator_mono le_sup_right le_rfl).trans data.product_action).trans
      (Subgroup.le_centralizer_iff.mp hZcentralV)
  refine ⟨hZelem, hQp, hEV.trans hZnormal, hQV.trans hZnormal, hQE, ?_⟩
  have hchar : IsCharacteristicTwoType P := by
    simpa only [hstep] using (edge_characteristic_data ctx.sectionSeven Γ cp).2
  have hfixedQ : Z ⊓ Subgroup.centralizer (Q : Set G) ≤ Q := by
    rw [hQeq]
    exact (le_inf (inf_le_left.trans (hZV.trans hVP))
      (by simpa only [hQeq] using (inf_le_right : Z ⊓ Subgroup.centralizer (Q : Set G) ≤
        Subgroup.centralizer (Q : Set G)))).trans
      (characteristic_centralizer_le_core P hchar)
  have hfixedZQ : Z ⊓ Subgroup.centralizer (Q : Set G) ≤
      (Subgroup.center Q).map Q.subtype := by
    intro x hx
    refine ⟨⟨x,hfixedQ hx⟩, ?_, rfl⟩
    apply Subgroup.mem_center_iff.mpr
    intro y
    exact Subtype.ext (hx.2 y y.property)
  have hcentral : ⁅(Subgroup.center Q).map Q.subtype, twoResidualIn P⁆ = ⊥ := by
    have heq := congrArg (fun b => ⁅(Subgroup.center (q Γ b)).map (q Γ b).subtype,
      twoResidualIn (stabilizer Γ b)⁆ = ⊥) hstep
    exact heq.mp (next_core_center_residual ctx.sectionSeven Γ cp ctx.commutator_eq)
  exact le_antisymm ((Subgroup.commutator_mono hfixedZQ
    (twoResidualIn_mono data.E P data.E_le)).trans hcentral.le) bot_le

public theorem distance_one_extracted_center_residual
    {H G : Type u} [Group H] [Finite H] [Group G] [Finite G]
    {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
    {embedding : G →* H} {T A B : Subgroup G}
    (ctx : AmbientSectionNineContext H S0 S P1 P2 embedding T A B)
    (hb : ctx.criticalPath.length = 1) (data : DistanceOneActionData ctx) :
    let next := ctx.Γ.act data.x⁻¹ ctx.criticalPath.a
    let C := z ctx.Γ ctx.criticalPath.a ⊓ stabilizer ctx.Γ next
    let D := z ctx.Γ next ⊓ stabilizer ctx.Γ ctx.criticalPath.a
    ⁅(Subgroup.center (C ⊔ D : Subgroup G)).map (C ⊔ D).subtype,
      twoResidualIn data.E⁆ = ⊥ := by
  obtain ⟨helem, hQ, hEN, hQN, hcomm, hfix⟩ :=
    distance_one_extracted_center_residual_inputs ctx hb data
  let _ := helem
  exact twoResidual_centralizes_of_commuting_fixed data.E _ _ hQ hEN hQN hcomm hfix

end Stellmacher.SectionNine
