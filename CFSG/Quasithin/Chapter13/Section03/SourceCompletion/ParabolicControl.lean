module
public import CFSG.Quasithin.Chapter13.Section03.SourceCompletion.ParabolicGeneration
public import CFSG.Quasithin.Chapter13.Section03.UnitaryGeometry.FlagFactorization
public import CFSG.Quasithin.Chapter13.Section03.LocalSteps
/-!
# Original unitary point and three-space normalizer control

The actual plane residual has cubic image and two-group plane kernel. The
preceding noncentrality theorem therefore makes the plane normalizer normalize
that residual. Generation by its three-space-normalizer conjugates and the
original TI property give C_G(V₃) ≤ N_G(V). The native derived point stabilizer
realizes every point-fixing automorphism of V₃, so an element normalizing both
V₁ and V₃ is a local element times an element of C_G(V₃).

Source: Aschbacher–Smith 13.3.15(6) and 13.3.17(1), printed pp.894–895.
The genuine preceding 13.3.14 noncentrality conclusion remains explicit.
-/
public section
namespace CFSG.Quasithin.Chapter13.Section03.SourceCompletion
open Subgroup ChapterE Atlas.G2.Natural.BinaryPointFlag
open scoped IsMulCommutative IsKleinFour
variable {G:Type*} [Group G] [Finite G] {V:Subgroup G} [IsElementaryAbelian 2 V]

omit [Finite G] in
private theorem flag_space_eq (E:Additive V≃ₗ[F]W) (A:Subgroup G) :
    pointCoordinateSubspace E A=(UnitaryGeometry.ambientSpace (V:=V) A).map E.toLinearMap := by
  ext w
  obtain ⟨v,rfl⟩:=E.surjective w
  rw [mem_pointCoordinateSubspace]
  constructor
  · intro hv;exact ⟨v,hv,rfl⟩
  · rintro ⟨x,hx,hxv⟩;exact E.injective hxv ▸ hx

theorem unitary_flag_normalizer_control
    (T:Sylow 2 G) (L Z B R:Subgroup G)
    (rho:Automizer V→*Atlas.G2.Model F) (E:Additive V≃ₗ[F]W)
    (he:∀a v,E (automizerRepresentation V a v)=
      Atlas.G2.Restricted.NaturalCoordinates.action F (rho a) (E v))
    (hz:pointCoordinateSubspace E Z=pointLine)
    (hp:pointCoordinateSubspace E B=plane) (hs:pointCoordinateSubspace E R=seed)
    (hZV:Z≤V) (hBV:B≤V) (hRV:R≤V)
    (hTZ:(T:Subgroup G)≤normalizer (Z:Set G))
    (hTB:(T:Subgroup G)≤normalizer (B:Set G))
    (hTL:(T:Subgroup G)≤normalizer (L:Set G))
    (hLN:L≤normalizer (V:Set G))
    (hfaith:L⊓centralizer (V:Set G)≤L.pCoreIn 2) (hres:pResidual 2 L=⊤)
    (hd:commutator (Atlas.G2.Model F)≤(inducedAutomizer V L).map rho)
    (hTI:∀g∈normalizer (L:Set G),V⊓V.map (MulAut.conj g).toMonoidHom=⊥ ∨
      V.map (MulAut.conj g).toMonoidHom=V)
    (hm:⁅(normalizer (Z:Set G)).pCoreIn 2,B⁆≠⊥) :
    centralizer (R:Set G)≤normalizer (V:Set G) ∧
      normalizer (Z:Set G)⊓normalizer (R:Set G)≤normalizer (V:Set G) := by
  have hZ:Nat.card Z=2:=by rw [←card_pointCoordinateSubspace E Z hZV,hz,card_pointLine]
  have hB:Nat.card B=4:=by rw [←card_pointCoordinateSubspace E B hBV,hp,card_plane]
  let : IsElementaryAbelian 2 B:=IsElementaryAbelian.of_le hBV
  let : Nontrivial B:=Finite.one_lt_card_iff_nontrivial.mp (by rw [hB];decide)
  let : IsKleinFour B:=⟨hB,IsElementaryAbelian.exponent_eq_prime⟩
  let : IsElementaryAbelian 2 R:=IsElementaryAbelian.of_le hRV
  have coord_le {A C:Subgroup G} (hAV:A≤V)
      (hh:pointCoordinateSubspace E A≤pointCoordinateSubspace E C) : A≤C := by
    intro a ha
    let v:Additive V:=Additive.ofMul ⟨a,hAV ha⟩
    exact (mem_pointCoordinateSubspace E C v).mp
      (hh ((mem_pointCoordinateSubspace E A v).mpr ha))
  have hZB:Z≤B:=coord_le hZV (by rw [hz,hp];exact pointLine_le_plane)
  have hBR:B≤R:=coord_le hBV (by rw [hp,hs];exact plane_le_seed)
  have hRne:R≠⊥ := by
    intro hb
    have hzbot:Z=⊥:=le_bot_iff.mp (hb ▸ hZB.trans hBR)
    rw [hzbot,Subgroup.card_bot] at hZ
    omega
  let K:=L⊓normalizer (B:Set G)
  let X:Subgroup G:=(pResidual 2 K).map K.subtype
  have hXL:X≤L:=(map_subtype_le _).trans inf_le_left
  have hXB:X≤normalizer (B:Set G):=(map_subtype_le _).trans inf_le_right
  have hTX:(T:Subgroup G)≤normalizer (X:Set G):=
    ((le_inf hTL (hTB.trans (normalizer (B:Set G)).le_normalizer)).trans
      inf_normalizer_le_normalizer_inf).trans
      (normalizer_le_normalizer_characteristic_image K (pResidual 2 K))
  have hX:IsPPerfect 2 X:=isPPerfect_embedded_pResidual 2 K
  have hc:=source_plane_residual_cubic L B rho E he hp hBV hLN hd
  have hx:=source_plane_action_card_three B X rho E he hp hXB hX hc
  have hkX:IsPGroup 2 (X⊓centralizer (B:Set G):Subgroup G):=
    (source_plane_centralizer_isTwo L B rho E he hp hLN hfaith).to_le
      (inf_le_inf_right _ hXL)
  have hNX:normalizer (B:Set G)≤normalizer (X:Set G):=
    (Chapter13.Section05.AmbientSource.plane_normalClosure T Z B X hZ hZB hTZ hTB
      hXB hTX hX hx hkX hm).2.1
  have hgen:=unitary_plane_residual_generation L B R rho E he hp hs hBV hRV hLN hfaith hres hd
  have hC:centralizer (R:Set G)≤normalizer (V:Set G) := by
    apply centralizer_le_normalizer_of_parabolic_generation V R L X
      (((centralizer_le hBR).trans (Subgroup.centralizer_le_normalizer _)).trans hNX)
      _ hTI hRne hRV
    refine hgen.symm.trans ?_
    unfold conjugateSpanBy
    congr 1
    ext x
    constructor
    · rintro ⟨l,hl,a,ha,h⟩;exact ⟨⟨l,hl⟩,⟨a,ha⟩,h.symm⟩
    · rintro ⟨l,a,h⟩;exact ⟨l.val,l.prop,a.val,a.prop,h.symm⟩
  refine ⟨hC,?_⟩
  have hRs:(UnitaryGeometry.ambientSpace (V:=V) R).map E.toLinearMap=
      Atlas.G2.Natural.BinaryIsotropicThree.target false := by
    rw [←flag_space_eq,hs]
    ext v;rw [mem_seed];rfl
  obtain ⟨E3,hE3⟩:=UnitaryGeometry.exists_three_coordinates hRV E hRs
  intro g hg
  have hpval:(E3.symm ![1,0,0]).toMul.val∈Z := by
    have hh:=hE3 (E3.symm ![1,0,0])
    rw [E3.apply_symm_apply] at hh
    let v:Additive V:=Additive.ofMul ⟨(E3.symm ![1,0,0]).toMul.val,
      hRV (E3.symm ![1,0,0]).toMul.prop⟩
    change v.toMul.val∈Z
    apply (mem_pointCoordinateSubspace E Z v).mp
    change E v=_ at hh
    rw [hz,hh,mem_pointLine]
    intro i hi
    fin_cases i <;> first | exact (hi rfl).elim | rfl
  have hpoint:Commute g (E3.symm ![1,0,0]).toMul.val :=
    (mem_centralizer_iff.mp (normalizer_le_centralizer_of_card_two Z hZ hg.1) _ hpval).symm
  obtain ⟨n,hn,hnc⟩:=UnitaryGeometry.point_three_factorization hRV E E3 hE3 rho he
    (fun d=>hd d.prop) g hg.2 hpoint
  have hh: n*(n⁻¹*g)∈normalizer (V:Set G):=
    (normalizer (V:Set G)).mul_mem (hLN hn) (hC hnc)
  simpa only [mul_inv_cancel_left] using hh
end CFSG.Quasithin.Chapter13.Section03.SourceCompletion
