module
public import Theory.SpecificGroups.Triality.ShortRootCentralizer.Containment
public import Theory.SpecificGroups.Triality.ConcreteBruhat.FixedCellCount
public import Theory.SpecificGroups.Triality.ParabolicLocalStructure

/-!
# Short-root centralizers in triality over the field of order two

The highest short-root involution fixes a tree in the native parabolic
hexagon. Its central rank-one subgroup contains an element of order three,
whereas the Borel has order 4096 times 7. Thus this subgroup cannot fix an
edge. The normalizer-fixed vertex must be the central vertex, placing the
full short-root centralizer in the central parabolic, including q = 2.
The exact positive intersection is Sylow by the local Levi projection.

These are the native centralizer and extremality inputs of Aschbacher--Smith
F.4.27(4)(ii) and F.4.40--42, printed pp.288,294--295. They are used on the
original endpoint marking in Chapter14/Section02/EightLargeParabolic/ShortCentralizer.
The fixed-path and Levi arguments follow the general-field Containment and
Sylow modules; the order-three obstruction supplies their missing binary case.
-/

public noncomputable section
open Subgroup
namespace Triality.Standard.ShortRootCentralizer
open Parabolics ConcreteBruhat RadicalCoordinates RadicalCoordinates.LeviCommutators
open GroupAction.EvenPolygon TwoLocalGeometry

private theorem fixed_neighbor (n : ℕ) (hn : 0 < n)
    (R J : Subgroup (BinaryCarrier n hn))
    (hT : ((incidenceGraph n hn).induce (fixedVertices R)).IsTree)
    (hJN : J ≤ normalizer (R : Set (BinaryCarrier n hn)))
    (x y : Vertex n hn) (hxR : x ∈ fixedVertices R) (hyR : y ∈ fixedVertices R)
    (hx : ∀ j ∈ J, j • x = x) (hy : ∀ j ∈ J, j • y = y) (hne : x ≠ y) :
    ∃ w : Vertex n hn, (incidenceGraph n hn).Adj x w ∧ ∀ j ∈ J, j • w = w := by
  let xR : fixedVertices R := ⟨x,hxR⟩
  let yR : fixedVertices R := ⟨y,hyR⟩
  obtain ⟨p,hp,huniq⟩ := hT.existsUnique_path xR yR
  have hnonnil : ¬ p.Nil := by
    intro hnil
    exact hne (congrArg Subtype.val hnil.eq)
  refine ⟨p.snd.val,p.adj_snd hnonnil,?_⟩
  intro j hj
  let f : ((incidenceGraph n hn).induce (fixedVertices R)) →g
      ((incidenceGraph n hn).induce (fixedVertices R)) :=
    ⟨fun v => ⟨j • v.val,normalizer_smul_mem_fixedVertices R (hJN hj) v.property⟩,
      fun h => smul_adj j h⟩
  have hxj : f xR = xR := Subtype.ext (hx j hj)
  have hyj : f yR = yR := Subtype.ext (hy j hj)
  let q := (p.map f).copy hxj hyj
  have hq : q.IsPath := by
    apply (SimpleGraph.Walk.isPath_copy ..).mpr
    apply hp.map
    intro a b hab
    exact Subtype.ext (MulAction.injective j (congrArg Subtype.val hab))
  have he := congrArg (fun w => (w.getVert 1).val) (huniq q hq)
  simp only [q,SimpleGraph.Walk.getVert_copy,SimpleGraph.Walk.getVert_map] at he
  exact he

private theorem card_dvd_of_fixed_neighbor (n : ℕ) (hn : 0 < n)
    (J : Subgroup (BinaryCarrier n hn))
    (hJ : J ≤ parabolic (binaryParameters n hn) .central)
    (w : Vertex n hn)
    (hw : (incidenceGraph n hn).Adj
      (CosetGeometry.base (parabolic (binaryParameters n hn)) .central) w)
    (hfix : ∀ j ∈ J, j • w = w) : Nat.card J ∣ Nat.card (borel (binaryParameters n hn)) := by
  let P := binaryParameters n hn
  have htype : w.type = Node.arms := by
    have hh : Node.central ≠ w.type := hw.1
    cases ht : w.type <;> simp_all
  obtain ⟨g,hg,hgw⟩ := (CosetGeometry.incident_base_iff _ _ _).mp hw.2
  have hew : g • CosetGeometry.base (parabolic P) .arms = w := by
    cases w with
    | mk a q =>
      change a = Node.arms at htype
      subst a
      change CosetGeometry.Vertex.mk Node.arms (g • ((1 : Carrier P) : Carrier P ⧸ parabolic P .arms)) = _
      simpa only [MulAction.Quotient.smul_mk,smul_eq_mul,mul_one] using
        congrArg (CosetGeometry.Vertex.mk Node.arms) hgw
  have hmap (j : J) : g⁻¹ * j.val * g ∈ borel P := by
    rw [←parabolic_inf_binary P rfl]
    refine ⟨?_,(parabolic P .central).mul_mem
      ((parabolic P .central).mul_mem ((parabolic P .central).inv_mem hg) (hJ j.property)) hg⟩
    rw [←CosetGeometry.stabilizer_base (parabolic P) .arms]
    change (g⁻¹ * j.val * g) • CosetGeometry.base (parabolic P) .arms = _
    rw [mul_smul,mul_smul,hew,hfix j j.property,←hew,inv_smul_smul]
  let f : J →* borel P := (((MulAut.conj g⁻¹).toMonoidHom).comp J.subtype).codRestrict _
    (fun j => by
      change g⁻¹ * j.val * (g⁻¹)⁻¹ ∈ borel P
      simpa only [inv_inv] using hmap j)
  apply card_dvd_of_injective f
  intro a b hab
  exact Subtype.ext ((MulAut.conj g⁻¹).injective (congrArg Subtype.val hab))

/-- The entire native short-root centralizer lies in the central parabolic at q = 2. -/
theorem centralizer_le_central_two
    (t : ExtensionField (binaryParameters 1 Nat.zero_lt_one)) (ht : t ≠ 0) :
    centralizer ({short (binaryParameters 1 Nat.zero_lt_one) rfl 2 t} : Set (BinaryCarrier 1 Nat.zero_lt_one)) ≤
      parabolic (binaryParameters 1 Nat.zero_lt_one) .central := by
  let P := binaryParameters 1 Nat.zero_lt_one
  let r := short P rfl 2 t
  let R := zpowers r
  let J := levi P .central
  let C := centralizer ({r} : Set (Carrier P))
  have hr : orderOf r = 2 := short_order P rfl t ht
  have hR : R ≠ ⊥ := by
    intro he
    have he1 : r = 1 := zpowers_eq_bot.mp he
    simp only [he1,orderOf_one] at hr
    omega
  have hpR : IsPGroup 2 R := by
    apply (IsPGroup.iff_card).mpr
    exact ⟨1, by rw [Nat.card_zpowers,hr,pow_one]⟩
  have hCN : C ≤ normalizer (R : Set (Carrier P)) := by
    change centralizer ({r} : Set (Carrier P)) ≤ _
    rw [←centralizer_closure ({r} : Set (Carrier P)),←zpowers_eq_closure]
    exact centralizer_le_normalizer _
  have hJC : J ≤ C := levi_central_le_centralizer P rfl t
  have hJP : J ≤ parabolic P .central := levi_le_parabolic P .central
  let a : J := ⟨(CentralRootSquare.orderThreeActor P rfl).val,
    (CentralRootSquare.range_centralActor P rfl).le
      ⟨CentralRootSquare.orderThreeMatrix P,rfl⟩⟩
  have ha : orderOf a = 3 := by
    rw [←Subgroup.orderOf_coe]
    exact (Subgroup.orderOf_coe (CentralRootSquare.orderThreeActor P rfl)).trans
      (CentralRootSquare.orderOf_orderThreeActor P rfl)
  have hthree : 3 ∣ Nat.card J := ha ▸ orderOf_dvd_natCard a
  have hΓ := (hexagonGeometry 1 Nat.zero_lt_one).toEvenPolygonAction
    (apartmentTranslates 1 Nat.zero_lt_one) (standardApartment_fixer_odd 1 Nat.zero_lt_one)
  have hedge := exists_fixed_edge 1 Nat.zero_lt_one R hpR
  have hT := fixed_graph_isTree hΓ R hR hpR hedge
  obtain ⟨v,hv⟩ := normalizer_fixed_vertex_of_fixed_edge hΓ R hR hpR hedge
  let b := CosetGeometry.base (parabolic P) .central
  have hb : b ∈ fixedVertices R := by
    intro a ha
    have hRP : R ≤ parabolic P .central := zpowers_le.mpr
      (radical_le_parabolic P .central (descendedRootSubgroup_le_radical P rfl .central
        (short_mem P rfl .central 2 trivial t)))
    have hmem : a ∈ MulAction.stabilizer (Carrier P) b := by
      rw [CosetGeometry.stabilizer_base]
      exact hRP ha
    exact hmem
  have hvR : v ∈ fixedVertices R := fun a ha => hv a (R.le_normalizer ha)
  have hbJ : ∀ a ∈ J, a • b = b := by
    intro a ha
    have hmem : a ∈ MulAction.stabilizer (Carrier P) b := by
      rw [CosetGeometry.stabilizer_base]
      exact hJP ha
    exact hmem
  have he : b = v := by
    by_contra hne
    obtain ⟨w,hw,hfix⟩ := fixed_neighbor 1 Nat.zero_lt_one R J hT (hJC.trans hCN)
      b v hb hvR hbJ (fun a ha => hv a (hCN (hJC ha))) hne
    have hd := hthree.trans (card_dvd_of_fixed_neighbor 1 Nat.zero_lt_one J hJP w hw hfix)
    rw [FixedCellCount.card_borel] at hd
    norm_num [Parameters.q,binaryParameters] at hd
  intro a ha
  rw [←CosetGeometry.stabilizer_base (parabolic P) .central]
  change a • b = b
  rw [he]
  exact hv a (hCN ha)


private theorem retract_sylow_bound {G Q : Type*} [Group G] [Group Q] [Finite G]
    (S : Sylow 2 G) (f : G →* Q) (hf : Function.Surjective f)
    (i : Q →* G) (hi : ∀ x, f (i x) = x) (hk : f.ker ≤ (S : Subgroup G))
    (D : Subgroup G) (hD : IsPGroup 2 D)
    (hrep : ∀ x ∈ (S : Subgroup G), i (f x) ∈ D) : D ≤ (S : Subgroup G) := by
  have hm : (S : Subgroup G).map f ≤ D.map f := by
    rintro _ ⟨x,hx,rfl⟩
    exact ⟨i (f x),hrep x hx,hi _⟩
  have he := (S.mapSurjective hf).is_maximal' (hD.map f) hm
  have hh := map_le_iff_le_comap.mp he.le
  change D ≤ ((S : Subgroup G).map f).comap f at hh
  rwa [comap_map_eq_self hk] at hh

private theorem retract_mem_sylow {G Q : Type*} [Group G] [Group Q]
    (S : Subgroup G) (f : G →* Q) (i : Q →* G) (hi : ∀ x, f (i x) = x)
    (hk : f.ker ≤ S) (x : G) (hx : x ∈ S) : i (f x) ∈ S := by
  rw [←comap_map_eq_self hk]
  change f (i (f x)) ∈ S.map f
  rw [hi]
  exact mem_map_of_mem f hx

/-- The designated positive intersection is Sylow in the full short-root
centralizer at q = 2, using the exact local Levi projection. -/
theorem centralizer_sylow_two
    (t : ExtensionField (binaryParameters 1 Nat.zero_lt_one)) (ht : t ≠ 0) :
    let P := binaryParameters 1 Nat.zero_lt_one
    ∃ R : Sylow 2 (centralizer ({short P rfl 2 t} : Set (Carrier P))),
      (R : Subgroup _) = (unipotent P).subgroupOf
        (centralizer ({short P rfl 2 t} : Set (Carrier P))) := by
  let P := binaryParameters 1 Nat.zero_lt_one
  let C := centralizer ({short P rfl 2 t} : Set (Carrier P))
  let F := localFactor P .central
  have hUC : IsPGroup 2 ((unipotent P).subgroupOf C) :=
    (unipotent_isPGroup_binary P rfl).comap_subtype
  refine ⟨⟨(unipotent P).subgroupOf C,hUC,?_⟩,rfl⟩
  intro D hD hUD
  apply le_antisymm ?_ hUD
  let A := D.map C.subtype
  have hAC : A ≤ C := map_subtype_le D
  have hAp : IsPGroup 2 A := hD.map C.subtype
  have hAF : A ≤ F := pSubgroup_le_localFactor P .central A hAp
    (hAC.trans (centralizer_le_central_two t ht))
  let S := (unipotentSylow P rfl).subtype (unipotentSylow_le_localFactor P rfl .central)
  let f := localLeviProjection P rfl .central
  let i := inclusion (levi_le_localFactor P rfl .central)
  have hi (x : levi P .central) : f (i x) = x := localLeviProjection_inclusion P rfl .central x
  have hRU : radical P .central ≤ unipotent P := by
    rw [radical_eq_descendedRootSubgroup P rfl .central]
    exact descendSubgroup_mono P (rootSubgroup_le_positiveSubgroup P rfl .central)
  have hk : f.ker ≤ (S : Subgroup F) := by
    rw [show f.ker = (radical P .central).subgroupOf F from
      localLeviProjection_ker P rfl .central]
    exact fun x hx => hRU hx
  have hAS : A.subgroupOf F ≤ (S : Subgroup F) := by
    apply retract_sylow_bound S f (localLeviProjection_surjective P rfl .central)
      i hi hk (A.subgroupOf F) hAp.comap_subtype
    intro x hx
    have hu : i (f x) ∈ (S : Subgroup F) := retract_mem_sylow _ f i hi hk x hx
    have hc : (i (f x)).val ∈ C := levi_central_le_centralizer P rfl t (f x).property
    exact mem_map_of_mem C.subtype (hUD (show (⟨(i (f x)).val,hc⟩ : C) ∈
      (unipotent P).subgroupOf C from hu))
  intro x hx
  exact hAS (show (⟨x.val,hAF (mem_map_of_mem C.subtype hx)⟩ : F) ∈ A.subgroupOf F from
    mem_map_of_mem C.subtype hx)


end Triality.Standard.ShortRootCentralizer
