module

public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.Density1792.RankOne.SingularMatrix.LeftExpression.InitialProducts.CheckArithmetic
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.Density1792.RankOne.SingularMatrix.LeftExpression.InitialProducts.Scalar10

/-!
# Exact product checks on rows 640 through 703

Literal masks are connected to the published lists and packed XOR definitions.
The scalar checks therefore apply to precisely the original checker.
See source/README.md.
-/

set_option Elab.async false

@[expose] public section
namespace Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.Density1792.RankOneCertificate.SingularMatrix.LeftCertificate.InitialProducts
namespace Block10

private theorem t_raw : Wide.checkRows 1792 t RightCertificate.wideSecond tb = true := by
  apply product_cons_b t640 tb640 ts640 _ _ ts640_sum ts640_parity
  apply product_cons_b t641 tb641 ts641 _ _ ts641_sum ts641_parity
  apply product_cons_b t642 tb642 ts642 _ _ ts642_sum ts642_parity
  apply product_cons_b t643 tb643 ts643 _ _ ts643_sum ts643_parity
  apply product_cons_b t644 tb644 ts644 _ _ ts644_sum ts644_parity
  apply product_cons_b t645 tb645 ts645 _ _ ts645_sum ts645_parity
  apply product_cons_b t646 tb646 ts646 _ _ ts646_sum ts646_parity
  apply product_cons_b t647 tb647 ts647 _ _ ts647_sum ts647_parity
  apply product_cons_b t648 tb648 ts648 _ _ ts648_sum ts648_parity
  apply product_cons_b t649 tb649 ts649 _ _ ts649_sum ts649_parity
  apply product_cons_b t650 tb650 ts650 _ _ ts650_sum ts650_parity
  apply product_cons_b t651 tb651 ts651 _ _ ts651_sum ts651_parity
  apply product_cons_b t652 tb652 ts652 _ _ ts652_sum ts652_parity
  apply product_cons_b t653 tb653 ts653 _ _ ts653_sum ts653_parity
  apply product_cons_b t654 tb654 ts654 _ _ ts654_sum ts654_parity
  apply product_cons_b t655 tb655 ts655 _ _ ts655_sum ts655_parity
  apply product_cons_b t656 tb656 ts656 _ _ ts656_sum ts656_parity
  apply product_cons_b t657 tb657 ts657 _ _ ts657_sum ts657_parity
  apply product_cons_b t658 tb658 ts658 _ _ ts658_sum ts658_parity
  apply product_cons_b t659 tb659 ts659 _ _ ts659_sum ts659_parity
  apply product_cons_b t660 tb660 ts660 _ _ ts660_sum ts660_parity
  apply product_cons_b t661 tb661 ts661 _ _ ts661_sum ts661_parity
  apply product_cons_b t662 tb662 ts662 _ _ ts662_sum ts662_parity
  apply product_cons_b t663 tb663 ts663 _ _ ts663_sum ts663_parity
  apply product_cons_b t664 tb664 ts664 _ _ ts664_sum ts664_parity
  apply product_cons_b t665 tb665 ts665 _ _ ts665_sum ts665_parity
  apply product_cons_b t666 tb666 ts666 _ _ ts666_sum ts666_parity
  apply product_cons_b t667 tb667 ts667 _ _ ts667_sum ts667_parity
  apply product_cons_b t668 tb668 ts668 _ _ ts668_sum ts668_parity
  apply product_cons_b t669 tb669 ts669 _ _ ts669_sum ts669_parity
  apply product_cons_b t670 tb670 ts670 _ _ ts670_sum ts670_parity
  apply product_cons_b t671 tb671 ts671 _ _ ts671_sum ts671_parity
  apply product_cons_b t672 tb672 ts672 _ _ ts672_sum ts672_parity
  apply product_cons_b t673 tb673 ts673 _ _ ts673_sum ts673_parity
  apply product_cons_b t674 tb674 ts674 _ _ ts674_sum ts674_parity
  apply product_cons_b t675 tb675 ts675 _ _ ts675_sum ts675_parity
  apply product_cons_b t676 tb676 ts676 _ _ ts676_sum ts676_parity
  apply product_cons_b t677 tb677 ts677 _ _ ts677_sum ts677_parity
  apply product_cons_b t678 tb678 ts678 _ _ ts678_sum ts678_parity
  apply product_cons_b t679 tb679 ts679 _ _ ts679_sum ts679_parity
  apply product_cons_b t680 tb680 ts680 _ _ ts680_sum ts680_parity
  apply product_cons_b t681 tb681 ts681 _ _ ts681_sum ts681_parity
  apply product_cons_b t682 tb682 ts682 _ _ ts682_sum ts682_parity
  apply product_cons_b t683 tb683 ts683 _ _ ts683_sum ts683_parity
  apply product_cons_b t684 tb684 ts684 _ _ ts684_sum ts684_parity
  apply product_cons_b t685 tb685 ts685 _ _ ts685_sum ts685_parity
  apply product_cons_b t686 tb686 ts686 _ _ ts686_sum ts686_parity
  apply product_cons_b t687 tb687 ts687 _ _ ts687_sum ts687_parity
  apply product_cons_b t688 tb688 ts688 _ _ ts688_sum ts688_parity
  apply product_cons_b t689 tb689 ts689 _ _ ts689_sum ts689_parity
  apply product_cons_b t690 tb690 ts690 _ _ ts690_sum ts690_parity
  apply product_cons_b t691 tb691 ts691 _ _ ts691_sum ts691_parity
  apply product_cons_b t692 tb692 ts692 _ _ ts692_sum ts692_parity
  apply product_cons_b t693 tb693 ts693 _ _ ts693_sum ts693_parity
  apply product_cons_b t694 tb694 ts694 _ _ ts694_sum ts694_parity
  apply product_cons_b t695 tb695 ts695 _ _ ts695_sum ts695_parity
  apply product_cons_b t696 tb696 ts696 _ _ ts696_sum ts696_parity
  apply product_cons_b t697 tb697 ts697 _ _ ts697_sum ts697_parity
  apply product_cons_b t698 tb698 ts698 _ _ ts698_sum ts698_parity
  apply product_cons_b t699 tb699 ts699 _ _ ts699_sum ts699_parity
  apply product_cons_b t700 tb700 ts700 _ _ ts700_sum ts700_parity
  apply product_cons_b t701 tb701 ts701 _ _ ts701_sum ts701_parity
  apply product_cons_b t702 tb702 ts702 _ _ ts702_sum ts702_parity
  apply product_cons_b t703 tb703 ts703 _ _ ts703_sum ts703_parity
  rfl

private theorem d_raw : Wide.checkRows 1792 d RightCertificate.wideFirst da = true := by
  apply product_cons_a d640 da640 ds640 _ _ ds640_sum ds640_parity
  apply product_cons_a d641 da641 ds641 _ _ ds641_sum ds641_parity
  apply product_cons_a d642 da642 ds642 _ _ ds642_sum ds642_parity
  apply product_cons_a d643 da643 ds643 _ _ ds643_sum ds643_parity
  apply product_cons_a d644 da644 ds644 _ _ ds644_sum ds644_parity
  apply product_cons_a d645 da645 ds645 _ _ ds645_sum ds645_parity
  apply product_cons_a d646 da646 ds646 _ _ ds646_sum ds646_parity
  apply product_cons_a d647 da647 ds647 _ _ ds647_sum ds647_parity
  apply product_cons_a d648 da648 ds648 _ _ ds648_sum ds648_parity
  apply product_cons_a d649 da649 ds649 _ _ ds649_sum ds649_parity
  apply product_cons_a d650 da650 ds650 _ _ ds650_sum ds650_parity
  apply product_cons_a d651 da651 ds651 _ _ ds651_sum ds651_parity
  apply product_cons_a d652 da652 ds652 _ _ ds652_sum ds652_parity
  apply product_cons_a d653 da653 ds653 _ _ ds653_sum ds653_parity
  apply product_cons_a d654 da654 ds654 _ _ ds654_sum ds654_parity
  apply product_cons_a d655 da655 ds655 _ _ ds655_sum ds655_parity
  apply product_cons_a d656 da656 ds656 _ _ ds656_sum ds656_parity
  apply product_cons_a d657 da657 ds657 _ _ ds657_sum ds657_parity
  apply product_cons_a d658 da658 ds658 _ _ ds658_sum ds658_parity
  apply product_cons_a d659 da659 ds659 _ _ ds659_sum ds659_parity
  apply product_cons_a d660 da660 ds660 _ _ ds660_sum ds660_parity
  apply product_cons_a d661 da661 ds661 _ _ ds661_sum ds661_parity
  apply product_cons_a d662 da662 ds662 _ _ ds662_sum ds662_parity
  apply product_cons_a d663 da663 ds663 _ _ ds663_sum ds663_parity
  apply product_cons_a d664 da664 ds664 _ _ ds664_sum ds664_parity
  apply product_cons_a d665 da665 ds665 _ _ ds665_sum ds665_parity
  apply product_cons_a d666 da666 ds666 _ _ ds666_sum ds666_parity
  apply product_cons_a d667 da667 ds667 _ _ ds667_sum ds667_parity
  apply product_cons_a d668 da668 ds668 _ _ ds668_sum ds668_parity
  apply product_cons_a d669 da669 ds669 _ _ ds669_sum ds669_parity
  apply product_cons_a d670 da670 ds670 _ _ ds670_sum ds670_parity
  apply product_cons_a d671 da671 ds671 _ _ ds671_sum ds671_parity
  apply product_cons_a d672 da672 ds672 _ _ ds672_sum ds672_parity
  apply product_cons_a d673 da673 ds673 _ _ ds673_sum ds673_parity
  apply product_cons_a d674 da674 ds674 _ _ ds674_sum ds674_parity
  apply product_cons_a d675 da675 ds675 _ _ ds675_sum ds675_parity
  apply product_cons_a d676 da676 ds676 _ _ ds676_sum ds676_parity
  apply product_cons_a d677 da677 ds677 _ _ ds677_sum ds677_parity
  apply product_cons_a d678 da678 ds678 _ _ ds678_sum ds678_parity
  apply product_cons_a d679 da679 ds679 _ _ ds679_sum ds679_parity
  apply product_cons_a d680 da680 ds680 _ _ ds680_sum ds680_parity
  apply product_cons_a d681 da681 ds681 _ _ ds681_sum ds681_parity
  apply product_cons_a d682 da682 ds682 _ _ ds682_sum ds682_parity
  apply product_cons_a d683 da683 ds683 _ _ ds683_sum ds683_parity
  apply product_cons_a d684 da684 ds684 _ _ ds684_sum ds684_parity
  apply product_cons_a d685 da685 ds685 _ _ ds685_sum ds685_parity
  apply product_cons_a d686 da686 ds686 _ _ ds686_sum ds686_parity
  apply product_cons_a d687 da687 ds687 _ _ ds687_sum ds687_parity
  apply product_cons_a d688 da688 ds688 _ _ ds688_sum ds688_parity
  apply product_cons_a d689 da689 ds689 _ _ ds689_sum ds689_parity
  apply product_cons_a d690 da690 ds690 _ _ ds690_sum ds690_parity
  apply product_cons_a d691 da691 ds691 _ _ ds691_sum ds691_parity
  apply product_cons_a d692 da692 ds692 _ _ ds692_sum ds692_parity
  apply product_cons_a d693 da693 ds693 _ _ ds693_sum ds693_parity
  apply product_cons_a d694 da694 ds694 _ _ ds694_sum ds694_parity
  apply product_cons_a d695 da695 ds695 _ _ ds695_sum ds695_parity
  apply product_cons_a d696 da696 ds696 _ _ ds696_sum ds696_parity
  apply product_cons_a d697 da697 ds697 _ _ ds697_sum ds697_parity
  apply product_cons_a d698 da698 ds698 _ _ ds698_sum ds698_parity
  apply product_cons_a d699 da699 ds699 _ _ ds699_sum ds699_parity
  apply product_cons_a d700 da700 ds700 _ _ ds700_sum ds700_parity
  apply product_cons_a d701 da701 ds701 _ _ ds701_sum ds701_parity
  apply product_cons_a d702 da702 ds702 _ _ ds702_sum ds702_parity
  apply product_cons_a d703 da703 ds703 _ _ ds703_sum ds703_parity
  rfl

set_option maxRecDepth 8192 in
private theorem a_rows : ((Data1792.firstRows.toList).drop 640).take 64 = a := by decide +kernel
set_option maxRecDepth 8192 in
private theorem b_rows : ((Data1792.secondRows.toList).drop 640).take 64 = b := by decide +kernel
set_option maxRecDepth 8192 in
private theorem tb_rows : ((tbRows).drop 640).take 64 = tb := by decide +kernel
set_option maxRecDepth 8192 in
private theorem da_rows : ((daRows).drop 640).take 64 = da := by decide +kernel
private theorem t_xor : List.zipWith Nat.xor a b = t := by decide +kernel
private theorem d_xor : List.zipWith Nat.xor t tb = d := by decide +kernel
private theorem t_rows : (tRows.drop 640).take 64 = t := by
  simp only [tRows, List.drop_zipWith, List.take_zipWith, a_rows, b_rows, t_xor]
private theorem d_rows : (dRows.drop 640).take 64 = d := by
  simp only [dRows, List.drop_zipWith, List.take_zipWith, t_rows, tb_rows, d_xor]

theorem tb_checked : Wide.checkRows 1792 ((tRows.drop 640).take 64) RightCertificate.wideSecond ((tbRows.drop 640).take 64) = true := by
  rw [t_rows, tb_rows]
  exact t_raw

theorem da_checked : Wide.checkRows 1792 ((dRows.drop 640).take 64) RightCertificate.wideFirst ((daRows.drop 640).take 64) = true := by
  rw [d_rows, da_rows]
  exact d_raw


end Block10
end Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.Density1792.RankOneCertificate.SingularMatrix.LeftCertificate.InitialProducts
