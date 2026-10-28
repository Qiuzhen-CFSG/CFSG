module

public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.Density1792.RankOne.SingularMatrix.LeftExpression.InitialProducts.CheckArithmetic
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.Density1792.RankOne.SingularMatrix.LeftExpression.InitialProducts.Scalar09

/-!
# Exact product checks on rows 576 through 639

Literal masks are connected to the published lists and packed XOR definitions.
The scalar checks therefore apply to precisely the original checker.
See source/README.md.
-/

set_option Elab.async false

@[expose] public section
namespace Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.Density1792.RankOneCertificate.SingularMatrix.LeftCertificate.InitialProducts
namespace Block09

private theorem t_raw : Wide.checkRows 1792 t RightCertificate.wideSecond tb = true := by
  apply product_cons_b t576 tb576 ts576 _ _ ts576_sum ts576_parity
  apply product_cons_b t577 tb577 ts577 _ _ ts577_sum ts577_parity
  apply product_cons_b t578 tb578 ts578 _ _ ts578_sum ts578_parity
  apply product_cons_b t579 tb579 ts579 _ _ ts579_sum ts579_parity
  apply product_cons_b t580 tb580 ts580 _ _ ts580_sum ts580_parity
  apply product_cons_b t581 tb581 ts581 _ _ ts581_sum ts581_parity
  apply product_cons_b t582 tb582 ts582 _ _ ts582_sum ts582_parity
  apply product_cons_b t583 tb583 ts583 _ _ ts583_sum ts583_parity
  apply product_cons_b t584 tb584 ts584 _ _ ts584_sum ts584_parity
  apply product_cons_b t585 tb585 ts585 _ _ ts585_sum ts585_parity
  apply product_cons_b t586 tb586 ts586 _ _ ts586_sum ts586_parity
  apply product_cons_b t587 tb587 ts587 _ _ ts587_sum ts587_parity
  apply product_cons_b t588 tb588 ts588 _ _ ts588_sum ts588_parity
  apply product_cons_b t589 tb589 ts589 _ _ ts589_sum ts589_parity
  apply product_cons_b t590 tb590 ts590 _ _ ts590_sum ts590_parity
  apply product_cons_b t591 tb591 ts591 _ _ ts591_sum ts591_parity
  apply product_cons_b t592 tb592 ts592 _ _ ts592_sum ts592_parity
  apply product_cons_b t593 tb593 ts593 _ _ ts593_sum ts593_parity
  apply product_cons_b t594 tb594 ts594 _ _ ts594_sum ts594_parity
  apply product_cons_b t595 tb595 ts595 _ _ ts595_sum ts595_parity
  apply product_cons_b t596 tb596 ts596 _ _ ts596_sum ts596_parity
  apply product_cons_b t597 tb597 ts597 _ _ ts597_sum ts597_parity
  apply product_cons_b t598 tb598 ts598 _ _ ts598_sum ts598_parity
  apply product_cons_b t599 tb599 ts599 _ _ ts599_sum ts599_parity
  apply product_cons_b t600 tb600 ts600 _ _ ts600_sum ts600_parity
  apply product_cons_b t601 tb601 ts601 _ _ ts601_sum ts601_parity
  apply product_cons_b t602 tb602 ts602 _ _ ts602_sum ts602_parity
  apply product_cons_b t603 tb603 ts603 _ _ ts603_sum ts603_parity
  apply product_cons_b t604 tb604 ts604 _ _ ts604_sum ts604_parity
  apply product_cons_b t605 tb605 ts605 _ _ ts605_sum ts605_parity
  apply product_cons_b t606 tb606 ts606 _ _ ts606_sum ts606_parity
  apply product_cons_b t607 tb607 ts607 _ _ ts607_sum ts607_parity
  apply product_cons_b t608 tb608 ts608 _ _ ts608_sum ts608_parity
  apply product_cons_b t609 tb609 ts609 _ _ ts609_sum ts609_parity
  apply product_cons_b t610 tb610 ts610 _ _ ts610_sum ts610_parity
  apply product_cons_b t611 tb611 ts611 _ _ ts611_sum ts611_parity
  apply product_cons_b t612 tb612 ts612 _ _ ts612_sum ts612_parity
  apply product_cons_b t613 tb613 ts613 _ _ ts613_sum ts613_parity
  apply product_cons_b t614 tb614 ts614 _ _ ts614_sum ts614_parity
  apply product_cons_b t615 tb615 ts615 _ _ ts615_sum ts615_parity
  apply product_cons_b t616 tb616 ts616 _ _ ts616_sum ts616_parity
  apply product_cons_b t617 tb617 ts617 _ _ ts617_sum ts617_parity
  apply product_cons_b t618 tb618 ts618 _ _ ts618_sum ts618_parity
  apply product_cons_b t619 tb619 ts619 _ _ ts619_sum ts619_parity
  apply product_cons_b t620 tb620 ts620 _ _ ts620_sum ts620_parity
  apply product_cons_b t621 tb621 ts621 _ _ ts621_sum ts621_parity
  apply product_cons_b t622 tb622 ts622 _ _ ts622_sum ts622_parity
  apply product_cons_b t623 tb623 ts623 _ _ ts623_sum ts623_parity
  apply product_cons_b t624 tb624 ts624 _ _ ts624_sum ts624_parity
  apply product_cons_b t625 tb625 ts625 _ _ ts625_sum ts625_parity
  apply product_cons_b t626 tb626 ts626 _ _ ts626_sum ts626_parity
  apply product_cons_b t627 tb627 ts627 _ _ ts627_sum ts627_parity
  apply product_cons_b t628 tb628 ts628 _ _ ts628_sum ts628_parity
  apply product_cons_b t629 tb629 ts629 _ _ ts629_sum ts629_parity
  apply product_cons_b t630 tb630 ts630 _ _ ts630_sum ts630_parity
  apply product_cons_b t631 tb631 ts631 _ _ ts631_sum ts631_parity
  apply product_cons_b t632 tb632 ts632 _ _ ts632_sum ts632_parity
  apply product_cons_b t633 tb633 ts633 _ _ ts633_sum ts633_parity
  apply product_cons_b t634 tb634 ts634 _ _ ts634_sum ts634_parity
  apply product_cons_b t635 tb635 ts635 _ _ ts635_sum ts635_parity
  apply product_cons_b t636 tb636 ts636 _ _ ts636_sum ts636_parity
  apply product_cons_b t637 tb637 ts637 _ _ ts637_sum ts637_parity
  apply product_cons_b t638 tb638 ts638 _ _ ts638_sum ts638_parity
  apply product_cons_b t639 tb639 ts639 _ _ ts639_sum ts639_parity
  rfl

private theorem d_raw : Wide.checkRows 1792 d RightCertificate.wideFirst da = true := by
  apply product_cons_a d576 da576 ds576 _ _ ds576_sum ds576_parity
  apply product_cons_a d577 da577 ds577 _ _ ds577_sum ds577_parity
  apply product_cons_a d578 da578 ds578 _ _ ds578_sum ds578_parity
  apply product_cons_a d579 da579 ds579 _ _ ds579_sum ds579_parity
  apply product_cons_a d580 da580 ds580 _ _ ds580_sum ds580_parity
  apply product_cons_a d581 da581 ds581 _ _ ds581_sum ds581_parity
  apply product_cons_a d582 da582 ds582 _ _ ds582_sum ds582_parity
  apply product_cons_a d583 da583 ds583 _ _ ds583_sum ds583_parity
  apply product_cons_a d584 da584 ds584 _ _ ds584_sum ds584_parity
  apply product_cons_a d585 da585 ds585 _ _ ds585_sum ds585_parity
  apply product_cons_a d586 da586 ds586 _ _ ds586_sum ds586_parity
  apply product_cons_a d587 da587 ds587 _ _ ds587_sum ds587_parity
  apply product_cons_a d588 da588 ds588 _ _ ds588_sum ds588_parity
  apply product_cons_a d589 da589 ds589 _ _ ds589_sum ds589_parity
  apply product_cons_a d590 da590 ds590 _ _ ds590_sum ds590_parity
  apply product_cons_a d591 da591 ds591 _ _ ds591_sum ds591_parity
  apply product_cons_a d592 da592 ds592 _ _ ds592_sum ds592_parity
  apply product_cons_a d593 da593 ds593 _ _ ds593_sum ds593_parity
  apply product_cons_a d594 da594 ds594 _ _ ds594_sum ds594_parity
  apply product_cons_a d595 da595 ds595 _ _ ds595_sum ds595_parity
  apply product_cons_a d596 da596 ds596 _ _ ds596_sum ds596_parity
  apply product_cons_a d597 da597 ds597 _ _ ds597_sum ds597_parity
  apply product_cons_a d598 da598 ds598 _ _ ds598_sum ds598_parity
  apply product_cons_a d599 da599 ds599 _ _ ds599_sum ds599_parity
  apply product_cons_a d600 da600 ds600 _ _ ds600_sum ds600_parity
  apply product_cons_a d601 da601 ds601 _ _ ds601_sum ds601_parity
  apply product_cons_a d602 da602 ds602 _ _ ds602_sum ds602_parity
  apply product_cons_a d603 da603 ds603 _ _ ds603_sum ds603_parity
  apply product_cons_a d604 da604 ds604 _ _ ds604_sum ds604_parity
  apply product_cons_a d605 da605 ds605 _ _ ds605_sum ds605_parity
  apply product_cons_a d606 da606 ds606 _ _ ds606_sum ds606_parity
  apply product_cons_a d607 da607 ds607 _ _ ds607_sum ds607_parity
  apply product_cons_a d608 da608 ds608 _ _ ds608_sum ds608_parity
  apply product_cons_a d609 da609 ds609 _ _ ds609_sum ds609_parity
  apply product_cons_a d610 da610 ds610 _ _ ds610_sum ds610_parity
  apply product_cons_a d611 da611 ds611 _ _ ds611_sum ds611_parity
  apply product_cons_a d612 da612 ds612 _ _ ds612_sum ds612_parity
  apply product_cons_a d613 da613 ds613 _ _ ds613_sum ds613_parity
  apply product_cons_a d614 da614 ds614 _ _ ds614_sum ds614_parity
  apply product_cons_a d615 da615 ds615 _ _ ds615_sum ds615_parity
  apply product_cons_a d616 da616 ds616 _ _ ds616_sum ds616_parity
  apply product_cons_a d617 da617 ds617 _ _ ds617_sum ds617_parity
  apply product_cons_a d618 da618 ds618 _ _ ds618_sum ds618_parity
  apply product_cons_a d619 da619 ds619 _ _ ds619_sum ds619_parity
  apply product_cons_a d620 da620 ds620 _ _ ds620_sum ds620_parity
  apply product_cons_a d621 da621 ds621 _ _ ds621_sum ds621_parity
  apply product_cons_a d622 da622 ds622 _ _ ds622_sum ds622_parity
  apply product_cons_a d623 da623 ds623 _ _ ds623_sum ds623_parity
  apply product_cons_a d624 da624 ds624 _ _ ds624_sum ds624_parity
  apply product_cons_a d625 da625 ds625 _ _ ds625_sum ds625_parity
  apply product_cons_a d626 da626 ds626 _ _ ds626_sum ds626_parity
  apply product_cons_a d627 da627 ds627 _ _ ds627_sum ds627_parity
  apply product_cons_a d628 da628 ds628 _ _ ds628_sum ds628_parity
  apply product_cons_a d629 da629 ds629 _ _ ds629_sum ds629_parity
  apply product_cons_a d630 da630 ds630 _ _ ds630_sum ds630_parity
  apply product_cons_a d631 da631 ds631 _ _ ds631_sum ds631_parity
  apply product_cons_a d632 da632 ds632 _ _ ds632_sum ds632_parity
  apply product_cons_a d633 da633 ds633 _ _ ds633_sum ds633_parity
  apply product_cons_a d634 da634 ds634 _ _ ds634_sum ds634_parity
  apply product_cons_a d635 da635 ds635 _ _ ds635_sum ds635_parity
  apply product_cons_a d636 da636 ds636 _ _ ds636_sum ds636_parity
  apply product_cons_a d637 da637 ds637 _ _ ds637_sum ds637_parity
  apply product_cons_a d638 da638 ds638 _ _ ds638_sum ds638_parity
  apply product_cons_a d639 da639 ds639 _ _ ds639_sum ds639_parity
  rfl

set_option maxRecDepth 8192 in
private theorem a_rows : ((Data1792.firstRows.toList).drop 576).take 64 = a := by decide +kernel
set_option maxRecDepth 8192 in
private theorem b_rows : ((Data1792.secondRows.toList).drop 576).take 64 = b := by decide +kernel
set_option maxRecDepth 8192 in
private theorem tb_rows : ((tbRows).drop 576).take 64 = tb := by decide +kernel
set_option maxRecDepth 8192 in
private theorem da_rows : ((daRows).drop 576).take 64 = da := by decide +kernel
private theorem t_xor : List.zipWith Nat.xor a b = t := by decide +kernel
private theorem d_xor : List.zipWith Nat.xor t tb = d := by decide +kernel
private theorem t_rows : (tRows.drop 576).take 64 = t := by
  simp only [tRows, List.drop_zipWith, List.take_zipWith, a_rows, b_rows, t_xor]
private theorem d_rows : (dRows.drop 576).take 64 = d := by
  simp only [dRows, List.drop_zipWith, List.take_zipWith, t_rows, tb_rows, d_xor]

theorem tb_checked : Wide.checkRows 1792 ((tRows.drop 576).take 64) RightCertificate.wideSecond ((tbRows.drop 576).take 64) = true := by
  rw [t_rows, tb_rows]
  exact t_raw

theorem da_checked : Wide.checkRows 1792 ((dRows.drop 576).take 64) RightCertificate.wideFirst ((daRows.drop 576).take 64) = true := by
  rw [d_rows, da_rows]
  exact d_raw


end Block09
end Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.Density1792.RankOneCertificate.SingularMatrix.LeftCertificate.InitialProducts
